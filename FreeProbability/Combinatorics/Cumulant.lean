import FreeProbability.Combinatorics.NoncrossingPartition
import FreeProbability.Algebraic.Distribution
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators

/-!
# Free cumulants by noncrossing recursion

The cumulant of a nonempty word is its moment minus the contributions of all
noncrossing partitions other than the one-block partition. Every recursive call
is on a strictly shorter block word. Empty cumulants are set to zero.
-/

namespace FreeProbability

variable {𝕜 X : Type*} [Field 𝕜]

/-- Read a block's positions in increasing order, preserving the order of letters. -/
def blockWord (w : List X) (s : Finset (Fin w.length)) : List X :=
  (s.sort (· ≤ ·)).map w.get

@[simp] theorem blockWord_length (w : List X) (s : Finset (Fin w.length)) :
    (blockWord w s).length = s.card := by simp [blockWord]

@[simp] theorem blockWord_univ (w : List X) : blockWord w Finset.univ = w := by
  simp only [blockWord, Fin.sort_univ]
  exact List.map_get_finRange w

/-- Proper noncrossing partitions exclude the full-word cumulant term. -/
abbrev ProperNoncrossingPartition (n : ℕ) :=
  {p : NoncrossingPartition n // p ≠ NoncrossingPartition.indiscrete n}

noncomputable instance (n : ℕ) : Fintype (ProperNoncrossingPartition n) := by
  classical
  exact Subtype.fintype _

/-- Free cumulants of any prescribed moment function, defined by genuine
well-founded noncrossing-partition inversion. -/
noncomputable def freeCumulant (moment : List X → 𝕜) (w : List X) : 𝕜 :=
  if w = [] then 0 else
    moment w - ∑ p : ProperNoncrossingPartition w.length,
      ∏ s ∈ p.val.blocks.attach, freeCumulant moment (blockWord w s.val)
termination_by w.length
decreasing_by
  simp only [blockWord_length]
  exact p.val.block_card_lt_of_ne_indiscrete p.property s.property

/-- The multiplicative contribution of a noncrossing partition. -/
noncomputable def partitionContribution (K : List X → 𝕜) (w : List X)
    (p : NoncrossingPartition w.length) : 𝕜 :=
  ∏ s ∈ p.blocks.attach, K (blockWord w s.val)

theorem partitionContribution_indiscrete (K : List X → 𝕜) (w : List X) (hw : w ≠ []) :
    partitionContribution K w (NoncrossingPartition.indiscrete w.length) = K w := by
  classical
  unfold partitionContribution
  rw [Finset.prod_attach _ (fun s => K (blockWord w s))]
  rw [NoncrossingPartition.blocks_indiscrete_of_pos (List.length_pos_iff.mpr hw)]
  simp

@[simp] theorem freeCumulant_nil (moment : List X → 𝕜) : freeCumulant moment [] = 0 := by
  rw [freeCumulant]
  simp

theorem freeCumulant_recursion (moment : List X → 𝕜) (w : List X) (hw : w ≠ []) :
    freeCumulant moment w = moment w -
      ∑ p : ProperNoncrossingPartition w.length,
        partitionContribution (freeCumulant moment) w p.val := by
  rw [freeCumulant]
  simp only [hw, ↓reduceIte, partitionContribution]

/-- The moment equals the full-word cumulant plus all proper-partition terms. -/
theorem moment_eq_cumulant_add_proper (moment : List X → 𝕜) (w : List X) (hw : w ≠ []) :
    moment w = freeCumulant moment w +
      ∑ p : ProperNoncrossingPartition w.length,
        partitionContribution (freeCumulant moment) w p.val := by
  rw [freeCumulant_recursion moment w hw]
  ring

/-- The full free moment–cumulant formula, summing over every noncrossing partition. -/
theorem moment_cumulant_formula (moment : List X → 𝕜) (w : List X) (hw : w ≠ []) :
    moment w = ∑ p : NoncrossingPartition w.length,
      partitionContribution (freeCumulant moment) w p := by
  classical
  rw [Fintype.sum_eq_add_sum_subtype_ne _ (NoncrossingPartition.indiscrete w.length),
    partitionContribution_indiscrete _ w hw]
  exact moment_eq_cumulant_add_proper moment w hw

@[simp] theorem partitionContribution_nil (K : List X → 𝕜)
    (p : NoncrossingPartition 0) : partitionContribution K [] p = 1 := by
  classical
  unfold partitionContribution
  rw [Finset.prod_attach _ (fun s => K (blockWord [] s)), NoncrossingPartition.blocks_zero]
  exact Finset.prod_empty

/-- Including the empty word, the formula holds for every normalized moment function. -/
theorem moment_cumulant_formula_all (moment : List X → 𝕜) (h0 : moment [] = 1) (w : List X) :
    moment w = ∑ p : NoncrossingPartition w.length,
      partitionContribution (freeCumulant moment) w p := by
  by_cases hw : w = []
  · subst w
    simp [h0]
  · exact moment_cumulant_formula moment w hw

/-- There is at most one cumulant family satisfying the noncrossing recursion
and the empty-word convention. -/
theorem freeCumulant_unique (moment : List X → 𝕜) (K : List X → 𝕜) (h0 : K [] = 0)
    (hK : ∀ w, w ≠ [] → K w = moment w -
      ∑ p : ProperNoncrossingPartition w.length, partitionContribution K w p.val) :
    K = freeCumulant moment := by
  funext w
  suffices ∀ n (w : List X), w.length = n → K w = freeCumulant moment w from
    this w.length w rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro w hw
    by_cases hnil : w = []
    · simp [hnil, h0]
    rw [hK w hnil, freeCumulant_recursion moment w hnil]
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.prod_congr rfl
    intro s _
    apply ih (blockWord w s.val).length
    · rw [blockWord_length, ← hw]
      exact p.val.block_card_lt_of_ne_indiscrete p.property s.property
    · rfl

/-- The full partition-sum formula also characterizes the constructed cumulants. -/
theorem freeCumulant_unique_of_moment_formula (moment : List X → 𝕜) (K : List X → 𝕜)
    (h0 : K [] = 0)
    (hK : ∀ w, w ≠ [] → moment w = ∑ p : NoncrossingPartition w.length,
      partitionContribution K w p) : K = freeCumulant moment := by
  classical
  apply freeCumulant_unique moment K h0
  intro w hw
  have hm := hK w hw
  rw [Fintype.sum_eq_add_sum_subtype_ne _ (NoncrossingPartition.indiscrete w.length),
    partitionContribution_indiscrete K w hw] at hm
  exact eq_sub_of_add_eq hm.symm

/-- Free cumulants associated to an algebraic expectation.
Multilinearity and mixed-cumulant vanishing will be proved separately. -/
noncomputable def cumulant {A : Type*} [Ring A] [Algebra 𝕜 A]
    (φ : ProbabilitySpace 𝕜 A) : List A → 𝕜 :=
  freeCumulant (fun w => φ.expectation w.prod)

theorem expectation_eq_sum_cumulants {A : Type*} [Ring A] [Algebra 𝕜 A]
    (φ : ProbabilitySpace 𝕜 A) (w : List A) :
    φ.expectation w.prod = ∑ p : NoncrossingPartition w.length,
      partitionContribution (cumulant φ) w p :=
  moment_cumulant_formula_all (fun w => φ.expectation w.prod) φ.map_one w

end FreeProbability

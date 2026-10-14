import FreeProbability.Combinatorics.BlockWordTransport
import FreeProbability.Combinatorics.CumulantMultilinear
import FreeProbability.Algebraic.CumulantFreeness
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Unit insertion and scalar shifts of free cumulants

Every cumulant of order at least two vanishes when one coordinate is the unit.
The proof uses the genuine singleton insertion bijection and all-order induction
on the blocks of proper noncrossing partitions. Scalar coordinates vanish by
multilinearity, so scalar shifts and centering preserve higher cumulants.
-/

namespace FreeProbability

variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]

omit [Ring A] in
/-- Ordered block words can equally be read from their ordered enumeration. -/
theorem orderedBlockWord_eq_ofFn {n : ℕ} (x : Fin n → A) (s : Finset (Fin n)) :
    orderedBlockWord x s = List.ofFn (x ∘ s.orderEmbOfFin rfl) := by
  rw [List.ofFn_eq_map, ← List.map_map, Finset.listMap_orderEmbOfFin_finRange]
  rfl

/-- The all-order moment–cumulant formula in tuple notation. -/
theorem expectation_eq_sum_orderedCumulants (φ : ProbabilitySpace 𝕜 A)
    {n : ℕ} (x : Fin n → A) :
    φ.expectation (List.ofFn x).prod = ∑ p : NoncrossingPartition n,
      orderedPartitionContribution (cumulant φ) x p := by
  have h := expectation_eq_sum_cumulants φ (List.ofFn x)
  simp only [← orderedPartitionContribution_get] at h
  exact h.trans (apply_ofFn_get (fun n x => ∑ p : NoncrossingPartition n,
    orderedPartitionContribution (cumulant φ) x p) x)

/-- Deleting a unit coordinate preserves the ordered product, without commutativity. -/
theorem prod_ofFn_remove_unit {n : ℕ} (x : Fin (n + 1) → A)
    (i : Fin (n + 1)) (hi : x i = 1) :
    (List.ofFn x).prod = (List.ofFn (x ∘ i.succAbove)).prod := by
  induction n with
  | zero =>
    have hi0 : i = 0 := Fin.eq_zero i
    subst i
    simp [List.ofFn_succ, hi]
  | succ n ih =>
    revert hi
    refine Fin.cases ?_ (fun i => ?_) i
    · intro hi
      simp [List.ofFn_succ, hi]
    · intro hi
      simp only [List.ofFn_succ, List.prod_cons]
      simp only [Function.comp_apply, Fin.succ_succAbove_zero, Fin.succ_succAbove_succ]
      congr 1
      have hh := ih (fun j => x j.succ) i hi
      rw [List.ofFn_succ, List.prod_cons] at hh
      exact hh

theorem orderedPartitionContribution_indiscrete (φ : ProbabilitySpace 𝕜 A)
    {n : ℕ} (x : Fin n → A) (hn : 0 < n) :
    orderedPartitionContribution (cumulant φ) x (NoncrossingPartition.indiscrete n) =
      cumulant φ (List.ofFn x) := by
  classical
  unfold orderedPartitionContribution
  rw [NoncrossingPartition.blocks_indiscrete_of_pos hn]
  simp only [Finset.prod_singleton]
  congr 1
  simp [orderedBlockWord, Fin.sort_univ, List.ofFn_eq_map]

/-- A nonsingleton block at a unit coordinate kills every proper contribution,
provided the smaller-order unit cumulants have already been proved. -/
theorem orderedContribution_zero_of_unit_induction (φ : ProbabilitySpace 𝕜 A)
    {n : ℕ} (x : Fin n → A) (i : Fin n) (hi : x i = 1)
    (ih : ∀ m < n, 2 ≤ m → ∀ (y : Fin m → A) (j : Fin m),
      y j = 1 → cumulant φ (List.ofFn y) = 0)
    (p : NoncrossingPartition n) (hp : p ≠ NoncrossingPartition.indiscrete n)
    (hns : ¬∀ j, p.val.r i j → j = i) :
    orderedPartitionContribution (cumulant φ) x p = 0 := by
  classical
  obtain ⟨s, ⟨hs, his⟩, _⟩ := p.existsUnique_block i
  have hs2 : 2 ≤ s.card := by
    by_contra h
    have hcard : s.card ≤ 1 := by omega
    apply hns
    intro j hij
    exact (Finset.card_le_one.mp hcard) j ((p.rel_iff_mem_block hs his j).mp hij) i his
  have hr : i ∈ Set.range (s.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]
    exact his
  obtain ⟨j, hj⟩ := hr
  unfold orderedPartitionContribution
  apply Finset.prod_eq_zero hs
  rw [orderedBlockWord_eq_ofFn]
  exact ih s.card (p.block_card_lt_of_ne_indiscrete hp hs) hs2
    (x ∘ s.orderEmbOfFin rfl) j (by simpa [Function.comp_apply, hj] using hi)

/-- Every free cumulant of order at least two containing a unit vanishes. -/
theorem cumulant_ofFn_eq_zero_of_unit (φ : ProbabilitySpace 𝕜 A) {n : ℕ}
    (hn : 2 ≤ n) (x : Fin n → A) (i : Fin n) (hi : x i = 1) :
    cumulant φ (List.ofFn x) = 0 := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => omega
    | succ n =>
      let P : NoncrossingPartition (n + 1) → Prop := fun p => ∀ j, p.val.r i j → j = i
      let F : NoncrossingPartition (n + 1) → 𝕜 := orderedPartitionContribution (cumulant φ) x
      have htop : ¬P (NoncrossingPartition.indiscrete (n + 1)) := by
        intro h
        have h0 := h ⟨0, by omega⟩ trivial
        have h1 := h ⟨1, by omega⟩ trivial
        have he : (0 : ℕ) = 1 := congrArg Fin.val (h0.trans h1.symm)
        omega
      let qtop : {p : NoncrossingPartition (n + 1) // ¬P p} :=
        ⟨NoncrossingPartition.indiscrete (n + 1), htop⟩
      have hnon : (∑ q : {p : NoncrossingPartition (n + 1) // ¬P p}, F q.val) =
          cumulant φ (List.ofFn x) := by
        rw [Fintype.sum_eq_single qtop]
        · exact orderedPartitionContribution_indiscrete φ x (by omega)
        · intro q hq
          apply orderedContribution_zero_of_unit_induction φ x i hi
          · intro m hm hm2 y j hy
            exact ih m hm hm2 y j hy
          · intro he
            exact hq (Subtype.ext he)
          · exact q.property
      have hsingle : (∑ q : {p : NoncrossingPartition (n + 1) // P p}, F q.val) =
          φ.expectation (List.ofFn x).prod := by
        change (∑ q : SingletonNoncrossingPartition i,
          orderedPartitionContribution (cumulant φ) x q.val) = _
        rw [sum_orderedPartitionContribution_singleton]
        have hc : cumulant φ [x i] = 1 := by
          simp [cumulant, hi, freeCumulant_singleton, φ.map_one]
        rw [hc, one_mul, ← expectation_eq_sum_orderedCumulants φ]
        exact congrArg φ.expectation (prod_ofFn_remove_unit x i hi).symm
      have hsum : (∑ q : {p : NoncrossingPartition (n + 1) // P p}, F q.val) +
          (∑ q : {p : NoncrossingPartition (n + 1) // ¬P p}, F q.val) = ∑ p, F p := by
        convert Fintype.sum_subtype_add_sum_subtype P F using 1
        congr 1; apply Finset.sum_congr
        all_goals first | (ext; simp) | (intro _ _; rfl)
      rw [hsingle, hnon] at hsum
      have hm := expectation_eq_sum_orderedCumulants φ x
      change φ.expectation (List.ofFn x).prod = ∑ p, F p at hm
      rw [← hm] at hsum
      exact add_left_cancel (hsum.trans (add_zero _).symm)

/-- List form of the unit insertion rule. -/
theorem cumulant_eq_zero_of_one_mem (φ : ProbabilitySpace 𝕜 A) (w : List A)
    (hlen : 2 ≤ w.length) (hone : (1 : A) ∈ w) : cumulant φ w = 0 := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hone
  simpa only [List.ofFn_get] using cumulant_ofFn_eq_zero_of_unit φ hlen w.get i hi

/-- A scalar coordinate in any order at least two has zero cumulant. -/
theorem cumulant_update_algebraMap (φ : ProbabilitySpace 𝕜 A) {n : ℕ}
    (hn : 2 ≤ n) (x : Fin n → A) (i : Fin n) (c : 𝕜) :
    cumulant φ (List.ofFn (Function.update x i (algebraMap 𝕜 A c))) = 0 := by
  classical
  rw [Algebra.algebraMap_eq_smul_one, cumulant_update_smul]
  rw [cumulant_ofFn_eq_zero_of_unit φ hn (Function.update x i 1) i (by simp), mul_zero]

/-- Higher cumulants are unchanged by a scalar shift of any coordinate. -/
theorem cumulant_update_add_algebraMap (φ : ProbabilitySpace 𝕜 A) {n : ℕ}
    (hn : 2 ≤ n) (x : Fin n → A) (i : Fin n) (a : A) (c : 𝕜) :
    cumulant φ (List.ofFn (Function.update x i (a + algebraMap 𝕜 A c))) =
      cumulant φ (List.ofFn (Function.update x i a)) := by
  rw [cumulant_update_add, cumulant_update_algebraMap φ hn, add_zero]

/-- Centering an individual coordinate preserves every higher free cumulant. -/
theorem cumulant_update_center (φ : ProbabilitySpace 𝕜 A) {n : ℕ}
    (hn : 2 ≤ n) (x : Fin n → A) (i : Fin n) :
    cumulant φ (List.ofFn (Function.update x i (φ.center (x i)))) =
      cumulant φ (List.ofFn x) := by
  classical
  have h := cumulant_update_add_algebraMap φ hn x i (φ.center (x i)) (φ.expectation (x i))
  rw [φ.center_add_expectation, Function.update_eq_self] at h
  exact h.symm

end FreeProbability

import FreeProbability.Combinatorics.AdjacentContributionGrouping
import FreeProbability.Combinatorics.OrderedAdjacentWord

/-!
# Consecutive interval fusion

A fusion plan successively multiplies neighboring entries. Its monotone,
surjective quotient maps the original positions to the final positions; hence
its fibers are nonempty intervals. No commutation of word entries is performed.
-/

namespace FreeProbability

/-- A finite sequence of multiplications of consecutive word entries. -/
inductive ConsecutiveFusion : ℕ → ℕ → Type
  | refl (n : ℕ) : ConsecutiveFusion n n
  | cons {n m : ℕ} (i : Fin n) (tail : ConsecutiveFusion n m) : ConsecutiveFusion (n + 1) m

namespace ConsecutiveFusion

variable {n m : ℕ}

/-- The final word after the prescribed consecutive multiplications. -/
def applyWord {A : Type*} [Monoid A] : {n m : ℕ} → ConsecutiveFusion n m → (Fin n → A) → Fin m → A
  | _, _, .refl _, x => x
  | _, _, .cons i t, x => applyWord t (fuseAdjacent x i)

/-- The monotone quotient of the original positions. -/
def quotient : {n m : ℕ} → ConsecutiveFusion n m → Fin n → Fin m
  | _, _, .refl _, a => a
  | _, _, .cons i t, a => quotient t (i.predAbove a)

theorem quotient_monotone (t : ConsecutiveFusion n m) : Monotone t.quotient := by
  induction t with
  | refl _ => exact monotone_id
  | cons i t ih => exact ih.comp i.predAbove_right_monotone

theorem quotient_surjective (t : ConsecutiveFusion n m) : Function.Surjective t.quotient := by
  induction t with
  | refl _ => exact Function.surjective_id
  | cons i t ih =>
    intro a
    obtain ⟨b, hb⟩ := ih a
    refine ⟨i.castSucc.succAbove b, ?_⟩
    simpa only [quotient, Fin.predAbove_succAbove] using hb

/-- Equal quotient positions contain every intermediate position. -/
theorem quotient_fiber_interval (t : ConsecutiveFusion n m) {a b c : Fin n}
    (hab : a ≤ b) (hbc : b ≤ c) (hac : t.quotient a = t.quotient c) :
    t.quotient b = t.quotient a := by
  apply le_antisymm
  · simpa only [hac] using t.quotient_monotone hbc
  · exact t.quotient_monotone hab

/-- Successive adjacent contractions of noncrossing partitions. -/
noncomputable def contract : {n m : ℕ} → ConsecutiveFusion n m →
    NoncrossingPartition n → NoncrossingPartition m
  | _, _, .refl _, p => p
  | _, _, .cons i t, p => contract t (p.contract i)

/-- Pull back a final partition through all interval fusions. -/
def expand : {n m : ℕ} → ConsecutiveFusion n m →
    NoncrossingPartition m → NoncrossingPartition n
  | _, _, .refl _, q => q
  | _, _, .cons i t, q => (expand t q).duplicate i

theorem expand_rel (t : ConsecutiveFusion n m) (q : NoncrossingPartition m) (a b : Fin n) :
    (t.expand q).val.r a b ↔ q.val.r (t.quotient a) (t.quotient b) := by
  induction t with
  | refl _ => rfl
  | cons i t ih => exact ih q (i.predAbove a) (i.predAbove b)

theorem contract_le_iff (t : ConsecutiveFusion n m) (p : NoncrossingPartition n)
    (q : NoncrossingPartition m) : t.contract p ≤ q ↔ p ≤ t.expand q := by
  induction t with
  | refl _ => rfl
  | cons i t ih => exact (ih _ q).trans (NoncrossingPartition.contract_le_iff _ _ i)

@[simp] theorem contract_expand (t : ConsecutiveFusion n m) (q : NoncrossingPartition m) :
    t.contract (t.expand q) = q := by
  induction t with
  | refl _ => rfl
  | cons i t ih => simpa only [contract, expand, NoncrossingPartition.contract_duplicate] using ih q

/-- The interval partition whose blocks are the consecutive fused groups. -/
def intervalPartition (t : ConsecutiveFusion n m) : NoncrossingPartition n :=
  t.expand (NoncrossingPartition.discrete m)

theorem intervalPartition_rel (t : ConsecutiveFusion n m) (a b : Fin n) :
    t.intervalPartition.val.r a b ↔ t.quotient a = t.quotient b := by
  rw [intervalPartition, expand_rel]
  rfl

/-- Duplication preserves noncrossing joins. -/
theorem duplicate_sup (p q : NoncrossingPartition n) (i : Fin n) :
    (p ⊔ q).duplicate i = p.duplicate i ⊔ q.duplicate i := by
  apply le_antisymm
  · have hr : (p.duplicate i ⊔ q.duplicate i).val.r i.castSucc i.succ :=
      (show p.duplicate i ≤ p.duplicate i ⊔ q.duplicate i from le_sup_left) (p.duplicate_adjacent i)
    rw [← (p.duplicate i ⊔ q.duplicate i).duplicate_erase i hr]
    apply (NoncrossingPartition.duplicate_le_duplicate_iff _ _ i).mpr
    apply sup_le
    · exact (NoncrossingPartition.duplicate_le_duplicate_iff _ _ i).mp
        (by rw [(p.duplicate i ⊔ q.duplicate i).duplicate_erase i hr]; exact le_sup_left)
    · exact (NoncrossingPartition.duplicate_le_duplicate_iff _ _ i).mp
        (by rw [(p.duplicate i ⊔ q.duplicate i).duplicate_erase i hr]; exact le_sup_right)
  · exact sup_le ((NoncrossingPartition.duplicate_le_duplicate_iff _ _ i).mpr le_sup_left)
      ((NoncrossingPartition.duplicate_le_duplicate_iff _ _ i).mpr le_sup_right)

/-- Pulling back the contraction adjoins exactly the consecutive interval groups. -/
theorem expand_contract (t : ConsecutiveFusion n m) (p : NoncrossingPartition n) :
    t.expand (t.contract p) = p ⊔ t.intervalPartition := by
  induction t with
  | refl n =>
    change p = p ⊔ NoncrossingPartition.discrete n
    rw [← NoncrossingPartition.bot_eq_discrete, sup_bot_eq]
  | cons i t ih =>
    change (t.expand (t.contract (p.contract i))).duplicate i =
      p ⊔ (t.expand (NoncrossingPartition.discrete _)).duplicate i
    rw [ih, duplicate_sup, NoncrossingPartition.duplicate_contract]
    change (p ⊔ NoncrossingPartition.adjacentPair i) ⊔ t.intervalPartition.duplicate i =
      p ⊔ t.intervalPartition.duplicate i
    have hle : NoncrossingPartition.adjacentPair i ≤ t.intervalPartition.duplicate i :=
      (NoncrossingPartition.adjacentPair_le_iff _ i).mpr
        (t.intervalPartition.duplicate_adjacent i)
    rw [sup_assoc, sup_eq_right.mpr hle]

/-- Equality of quotient partitions is exactly the corresponding interval-join fiber. -/
theorem contract_eq_iff (t : ConsecutiveFusion n m) (p : NoncrossingPartition n)
    (q : NoncrossingPartition m) :
    t.contract p = q ↔ p ⊔ t.intervalPartition = t.expand q := by
  constructor
  · intro h
    rw [← t.expand_contract p, h]
  · intro h
    have he : t.expand (t.contract p) = t.expand q := by rwa [t.expand_contract]
    simpa only [contract_expand] using congrArg t.contract he

@[simp] theorem expand_top (t : ConsecutiveFusion n m) :
    t.expand (⊤ : NoncrossingPartition m) = ⊤ := by
  exact le_antisymm le_top ((t.contract_le_iff _ _).mp le_top)

/-- Consecutive multiplication preserves the full ordered word product. -/
theorem prod_applyWord {A : Type*} [Monoid A] (t : ConsecutiveFusion n m)
    (x : Fin n → A) : (List.ofFn (t.applyWord x)).prod = (List.ofFn x).prod := by
  induction t with
  | refl _ => rfl
  | cons i t ih =>
    exact (ih (fuseAdjacent x i)).trans (prod_ofFn_fuseAdjacent x i)

end ConsecutiveFusion
end FreeProbability

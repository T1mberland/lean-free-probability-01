import FreeProbability.RandomMatrix.OrthogonalMultiTraceBounds
import Mathlib.GroupTheory.Perm.Fin

/-! # Actual products of permutation networks -/

noncomputable section
open scoped Classical
namespace FreeProbability.Orthogonal
open Equiv.Perm

variable {α β n : Type*} [Fintype α] [Fintype β] [Fintype n]

/-- Disjoint index cycles factor the actual finite coloring sum. -/
theorem permutationNetwork_sumCongr (σ : Equiv.Perm α) (τ : Equiv.Perm β)
    (M : α → Matrix n n ℂ) (L : β → Matrix n n ℂ) :
    permutationNetwork (Equiv.sumCongr σ τ) (Sum.elim M L) =
      permutationNetwork σ M * permutationNetwork τ L := by
  let : DecidableEq (α ⊕ β) := Classical.decEq _
  unfold permutationNetwork
  let F : (α ⊕ β → n) → ℂ := fun u =>
    ∏ a, (Sum.elim M L a) (u a) (u ((Equiv.sumCongr σ τ) a))
  change (∑ u, F u) = _
  rw [← (Equiv.sumArrowEquivProdArrow α β n).symm.sum_comp F]
  dsimp only [F]
  simp only [Fintype.sum_prod_type, Fintype.prod_sum_type,
    Equiv.sumArrowEquivProdArrow_symm_apply_inl,
    Equiv.sumArrowEquivProdArrow_symm_apply_inr, Equiv.sumCongr_apply,
    Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.mul_sum]

omit [Fintype α] [Fintype β] in
private theorem sumCongr_zpow (σ : Equiv.Perm α) (τ : Equiv.Perm β) (k : ℤ) :
    (Equiv.sumCongr σ τ) ^ k = Equiv.sumCongr (σ ^ k) (τ ^ k) := by
  simpa using ((Equiv.Perm.sumCongrHom α β).map_zpow (σ, τ) k).symm

omit [Fintype α] [Fintype β] in
/-- Actual orbits on the left summand are exactly its original orbits. -/
theorem sameCycle_sumCongr_inl (σ : Equiv.Perm α) (τ : Equiv.Perm β) (a b : α) :
    SameCycle (Equiv.sumCongr σ τ) (Sum.inl a) (Sum.inl b) ↔ SameCycle σ a b := by
  simp only [SameCycle, sumCongr_zpow, Equiv.sumCongr_apply, Sum.map_inl, Sum.inl.injEq]

omit [Fintype α] [Fintype β] in
/-- Actual orbits on the right summand are exactly its original orbits. -/
theorem sameCycle_sumCongr_inr (σ : Equiv.Perm α) (τ : Equiv.Perm β) (a b : β) :
    SameCycle (Equiv.sumCongr σ τ) (Sum.inr a) (Sum.inr b) ↔ SameCycle τ a b := by
  simp only [SameCycle, sumCongr_zpow, Equiv.sumCongr_apply, Sum.map_inr, Sum.inr.injEq]

omit [Fintype α] [Fintype β] in
/-- Disjoint summands cannot belong to the same actual permutation orbit. -/
theorem not_sameCycle_sumCongr_inl_inr (σ : Equiv.Perm α) (τ : Equiv.Perm β)
    (a : α) (b : β) : ¬ SameCycle (Equiv.sumCongr σ τ) (Sum.inl a) (Sum.inr b) := by
  simp only [SameCycle, sumCongr_zpow, Equiv.sumCongr_apply, Sum.map_inl,
    Sum.inl_ne_inr, exists_false, not_false_eq_true]

/-- All actual cycles of a disjoint sum, including fixed singleton cycles,
are precisely the disjoint sum of the original cycle indices. -/
def permutationOrbitSumEquiv (σ : Equiv.Perm α) (τ : Equiv.Perm β) :
    PermutationOrbitIndex (Equiv.sumCongr σ τ) ≃
      PermutationOrbitIndex σ ⊕ PermutationOrbitIndex τ where
  toFun := Quotient.lift (Sum.elim (fun a => Sum.inl (Quotient.mk _ a))
    (fun b => Sum.inr (Quotient.mk _ b))) (by
      intro a b h
      cases a with
      | inl a =>
        cases b with
        | inl b => exact congrArg Sum.inl (Quotient.sound ((sameCycle_sumCongr_inl σ τ a b).mp h))
        | inr b => exact False.elim (not_sameCycle_sumCongr_inl_inr σ τ a b h)
      | inr a =>
        cases b with
        | inl b => exact False.elim (not_sameCycle_sumCongr_inl_inr σ τ b a (SameCycle.symm h))
        | inr b => exact congrArg Sum.inr (Quotient.sound ((sameCycle_sumCongr_inr σ τ a b).mp h)))
  invFun := Sum.elim
    (Quotient.map Sum.inl (fun a b h => (sameCycle_sumCongr_inl σ τ a b).mpr h))
    (Quotient.map Sum.inr (fun a b h => (sameCycle_sumCongr_inr σ τ a b).mpr h))
  left_inv := by
    intro c
    induction c using Quotient.inductionOn with
    | h a => cases a <;> rfl
  right_inv := by
    intro c
    cases c with
    | inl c => induction c using Quotient.inductionOn; rfl
    | inr c => induction c using Quotient.inductionOn; rfl

/-- Actual cycle counts add for a disjoint sum of permutations. -/
theorem permutationOrbit_sumCongr_card (σ : Equiv.Perm α) (τ : Equiv.Perm β) :
    Fintype.card (PermutationOrbitIndex (Equiv.sumCongr σ τ)) =
      Fintype.card (PermutationOrbitIndex σ) + Fintype.card (PermutationOrbitIndex τ) := by
  rw [Fintype.card_congr (permutationOrbitSumEquiv σ τ), Fintype.card_sum]

/-- Reindexing sites transports the actual network without changing its value. -/
theorem permutationNetwork_permCongr (e : α ≃ β) (σ : Equiv.Perm α)
    (M : α → Matrix n n ℂ) :
    permutationNetwork (e.permCongr σ) (fun b => M (e.symm b)) =
      permutationNetwork σ M := by
  let : DecidableEq α := Classical.decEq _
  let : DecidableEq β := Classical.decEq _
  unfold permutationNetwork
  let F : (β → n) → ℂ := fun u => ∏ b, M (e.symm b) (u b) (u ((e.permCongr σ) b))
  change (∑ u, F u) = _
  rw [← (Equiv.arrowCongr e (Equiv.refl n)).sum_comp F]
  apply Finset.sum_congr rfl
  intro u _
  dsimp only [F]
  rw [← e.prod_comp]
  simp [Equiv.arrowCongr_apply]

omit [Fintype α] [Fintype β] in
/-- Reindexing preserves the actual integer-power orbit relation. -/
theorem sameCycle_permCongr (e : α ≃ β) (σ : Equiv.Perm α) (a b : α) :
    SameCycle (e.permCongr σ) (e a) (e b) ↔ SameCycle σ a b := by
  have hp (k : ℤ) : (e.permCongr σ) ^ k = e.permCongr (σ ^ k) :=
    (e.permCongrHom.toMonoidHom.map_zpow σ k).symm
  simp only [SameCycle, hp, Equiv.permCongr_apply, Equiv.symm_apply_apply,
    Equiv.apply_eq_iff_eq]

/-- Actual cycle indices transport bijectively under site reindexing. -/
def permutationOrbitTransportEquiv (e : α ≃ β) (σ : Equiv.Perm α) :
    PermutationOrbitIndex σ ≃ PermutationOrbitIndex (e.permCongr σ) where
  toFun := Quotient.map e (fun a b h => (sameCycle_permCongr e σ a b).mpr h)
  invFun := Quotient.map e.symm (by
    intro a b h
    change SameCycle (e.permCongr σ) a b at h
    exact (sameCycle_permCongr e σ (e.symm a) (e.symm b)).mp (by simpa using h))
  left_inv := by
    intro c
    induction c using Quotient.inductionOn with
    | h a => simp only [Quotient.map_mk, Equiv.symm_apply_apply]
  right_inv := by
    intro c
    induction c using Quotient.inductionOn with
    | h b => simp only [Quotient.map_mk, Equiv.apply_symm_apply]

/-- Reindexing changes no actual cycle count. -/
theorem permutationOrbit_permCongr_card (e : α ≃ β) (σ : Equiv.Perm α) :
    Fintype.card (PermutationOrbitIndex (e.permCongr σ)) =
      Fintype.card (PermutationOrbitIndex σ) :=
  (Fintype.card_congr (permutationOrbitTransportEquiv e σ)).symm

/-- A positive cyclic index has exactly one actual orbit, also in length one. -/
theorem permutationOrbit_finRotate_card {r : ℕ} (hr : 0 < r) :
    Fintype.card (PermutationOrbitIndex (finRotate r)) = 1 := by
  have h (a b : Fin r) : SameCycle (finRotate r) a b := by
    cases r with
    | zero => omega
    | succ r =>
      cases r with
      | zero =>
        have hab : a = b := by apply Fin.ext; omega
        rw [hab]
      | succ r =>
        apply (isCycle_finRotate (n := r)).sameCycle
        · apply mem_support.mp
          rw [support_finRotate]
          exact Finset.mem_univ _
        · apply mem_support.mp
          rw [support_finRotate]
          exact Finset.mem_univ _
  apply Fintype.card_eq_one_of_forall_eq (i := Quotient.mk _ (⟨0, hr⟩ : Fin r))
  intro c
  induction c using Quotient.inductionOn with
  | h a => exact Quotient.sound (h a _)

/-- The two genuine disjoint cyclic words, transported to the expansion's indices. -/
def twoTracePermutation (r s : ℕ) : Equiv.Perm (Fin (r + s)) :=
  finSumFinEquiv.permCongr (Equiv.sumCongr (finRotate r) (finRotate s))

/-- Concatenated matrix labels by their actual disjoint-sum site equivalence. -/
def twoTraceMatrices {r s : ℕ} (A : Fin r → Matrix n n ℂ) (C : Fin s → Matrix n n ℂ) :
    Fin (r + s) → Matrix n n ℂ := fun k => Sum.elim A C (finSumFinEquiv.symm k)

/-- Two positive words have exactly two actual trace cycles. -/
theorem twoTracePermutation_orbit_card {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    Fintype.card (PermutationOrbitIndex (twoTracePermutation r s)) = 2 := by
  rw [twoTracePermutation, permutationOrbit_permCongr_card, permutationOrbit_sumCongr_card,
    permutationOrbit_finRotate_card hr, permutationOrbit_finRotate_card hs]

variable [DecidableEq n]

/-- A positive cyclic network is the actual ordered matrix trace. -/
theorem permutationNetwork_finRotate {r : ℕ} (hr : 0 < r)
    (M : Fin r → Matrix n n ℂ) :
    permutationNetwork (finRotate r) M = Matrix.trace (List.ofFn M).prod := by
  rw [trace_ordered_product_eq_cyclic_sum hr]
  unfold permutationNetwork
  apply Finset.sum_congr (by ext u; simp)
  intro u _
  rfl

/-- The actual two-trace observable is the product of the two actual single
trace observables evaluated at the SAME Haar matrix. -/
theorem multiTraceWord_twoTrace {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (A B : Fin r → Matrix n n ℂ) (C D : Fin s → Matrix n n ℂ) (U : Group n) :
    multiTraceWord (twoTracePermutation r s) (twoTraceMatrices A C) (twoTraceMatrices B D) U =
      traceWord A B U * traceWord C D U := by
  have he : (fun k => complexMatrix U * twoTraceMatrices A C k *
      (complexMatrix U).transpose * twoTraceMatrices B D k) =
      (fun k => (Sum.elim (fun i => complexMatrix U * A i * (complexMatrix U).transpose * B i)
        (fun i => complexMatrix U * C i * (complexMatrix U).transpose * D i))
        (finSumFinEquiv.symm k)) := by
    funext k
    cases h : finSumFinEquiv.symm k <;> simp [twoTraceMatrices, h]
  unfold multiTraceWord
  rw [twoTracePermutation_orbit_card hr hs, he]
  unfold twoTracePermutation
  rw [permutationNetwork_permCongr, permutationNetwork_sumCongr]
  rw [permutationNetwork_finRotate hr, permutationNetwork_finRotate hs]
  unfold traceWord normalizedTrace
  ring

end FreeProbability.Orthogonal

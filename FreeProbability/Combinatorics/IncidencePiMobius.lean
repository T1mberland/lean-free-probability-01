import FreeProbability.Combinatorics.IncidenceOrderIso
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Möbius functions of finite products of finite posets -/

namespace FreeProbability

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {P : ι → Type*}
  [∀ i, Fintype (P i)] [∀ i, PartialOrder (P i)]
  [∀ i, LocallyFiniteOrder (P i)] [LocallyFiniteOrder (∀ i, P i)]

private theorem sum_Icc_prod {𝕜 : Type*} [CommSemiring 𝕜]
    (a b : ∀ i, P i) (f : ∀ i, P i → 𝕜) :
    (∑ x ∈ Finset.Icc a b, ∏ i, f i (x i)) =
      ∏ i, ∑ x ∈ Finset.Icc (a i) (b i), f i x := by
  classical
  let e : {x : ∀ i, P i // a ≤ x ∧ x ≤ b} ≃
      (∀ i, {x : P i // a i ≤ x ∧ x ≤ b i}) :=
    { toFun := fun x i => ⟨x.val i, x.property.1 i, x.property.2 i⟩
      invFun := fun x => ⟨fun i => (x i).val, fun i => (x i).property.1, fun i => (x i).property.2⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => funext (fun _ => Subtype.ext rfl) }
  rw [Finset.sum_subtype (Finset.Icc a b) (fun x => Finset.mem_Icc)
    (fun x => ∏ i, f i (x i))]
  trans ∑ x : (∀ i, {x : P i // a i ≤ x ∧ x ≤ b i}), ∏ i, f i (x i).val
  · exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  · trans ∏ i, ∑ x : {x : P i // a i ≤ x ∧ x ≤ b i}, f i x.val
    · exact (Fintype.prod_sum (fun i (x : {x : P i // a i ≤ x ∧ x ≤ b i}) => f i x.val)).symm
    · apply Finset.prod_congr rfl
      intro i _
      exact (Finset.sum_subtype (Finset.Icc (a i) (b i)) (fun x => Finset.mem_Icc) (f i)).symm

variable {𝕜 : Type*} [CommRing 𝕜] [∀ i, DecidableEq (P i)] [DecidableEq (∀ i, P i)]

private noncomputable def piMobiusCandidate : IncidenceAlgebra 𝕜 (∀ i, P i) where
  toFun a b := ∏ i, IncidenceAlgebra.mu 𝕜 (a i) (b i)
  eq_zero_of_not_le' := by
    classical
    intro a b h
    change ¬ ∀ i, a i ≤ b i at h
    push Not at h
    obtain ⟨i, hi⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (IncidenceAlgebra.apply_eq_zero_of_not_le hi _)

/-- The actual Möbius function of a finite dependent product of finite posets
is the product of the actual coordinate Möbius functions. -/
theorem incidence_mu_pi (a b : ∀ i, P i) :
    IncidenceAlgebra.mu 𝕜 a b = ∏ i, IncidenceAlgebra.mu 𝕜 (a i) (b i) := by
  classical
  let m : IncidenceAlgebra 𝕜 (∀ i, P i) := piMobiusCandidate
  have hm : m * IncidenceAlgebra.zeta 𝕜 = 1 := by
    ext a b
    rw [IncidenceAlgebra.mul_apply]
    change (∑ x ∈ Finset.Icc a b,
      (∏ i, IncidenceAlgebra.mu 𝕜 (a i) (x i)) * (if x ≤ b then 1 else 0)) =
      if a = b then 1 else 0
    calc
      _ = ∑ x ∈ Finset.Icc a b, ∏ i, IncidenceAlgebra.mu 𝕜 (a i) (x i) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [ite_eq_left (Finset.mem_Icc.mp hx).2, mul_one]
      _ = ∏ i, ∑ x ∈ Finset.Icc (a i) (b i), IncidenceAlgebra.mu 𝕜 (a i) x :=
        sum_Icc_prod a b _
      _ = ∏ i, if a i = b i then (1 : 𝕜) else 0 := by
        simp only [IncidenceAlgebra.sum_Icc_mu_right]
      _ = if a = b then 1 else 0 := by
        by_cases hab : a = b
        · subst b
          simp
        · have hi : ∃ i, a i ≠ b i := by
            by_contra h
            push Not at h
            exact hab (funext h)
          obtain ⟨i, hi⟩ := hi
          rw [ite_eq_right hab]
          exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
  have he : m = IncidenceAlgebra.mu 𝕜 :=
    left_inv_eq_right_inv hm IncidenceAlgebra.zeta_mul_mu
  exact (congrArg (fun v : IncidenceAlgebra 𝕜 (∀ i, P i) => v a b) he).symm

end FreeProbability

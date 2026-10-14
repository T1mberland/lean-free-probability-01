import FreeProbability.Fock.SecondQuantizationCompression
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap

/-! # Genuine block-operator realization of finite C-star matrices -/
noncomputable section
open scoped Classical InnerProductSpace

namespace FreeProbability.Fock
section Blocks
variable {N E : Type*} [Fintype N] [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [CompleteSpace E]

abbrev HilbertMatrixSpace (N E : Type*) [NormedAddCommGroup E] := lp (fun _ : N => E) 2

/-- The actual operator represented by a finite matrix of bounded Hilbert operators. -/
def hilbertMatrixOperator (M : Matrix N N (E →L[ℂ] E)) :
    HilbertMatrixSpace N E →L[ℂ] HilbertMatrixSpace N E :=
  ∑ i, ∑ j, (lp.singleContinuousLinearMap ℂ (fun _ : N => E) 2 i).comp
    ((M i j).comp (lp.evalCLM ℂ (fun _ : N => E) 2 j))

omit [CompleteSpace E] in
@[simp] theorem hilbertMatrixOperator_apply (M : Matrix N N (E →L[ℂ] E))
    (f : HilbertMatrixSpace N E) (i : N) :
    hilbertMatrixOperator M f i = ∑ j, M i j (f j) := by
  classical
  change (lp.evalCLM ℂ (fun _ : N => E) 2 i) (hilbertMatrixOperator M f) = _
  simp only [hilbertMatrixOperator, sum_apply, ContinuousLinearMap.comp_apply]
  rw [map_sum]
  simp only [map_sum]
  change (∑ x, ∑ j, (lp.single 2 x (M x j (f j))) i) = _
  simp [lp.single_apply, Pi.single_apply]


/-- Block extraction from an arbitrary bounded operator on the finite Hilbert sum. -/
def hilbertOperatorMatrix (T : HilbertMatrixSpace N E →L[ℂ] HilbertMatrixSpace N E) :
    Matrix N N (E →L[ℂ] E) := fun i j =>
  (lp.evalCLM ℂ (fun _ : N => E) 2 i).comp
    (T.comp (lp.singleContinuousLinearMap ℂ (fun _ : N => E) 2 j))

omit [CompleteSpace E] in
@[simp] theorem hilbertOperatorMatrix_operator (M : Matrix N N (E →L[ℂ] E)) :
    hilbertOperatorMatrix (hilbertMatrixOperator M) = M := by
  classical
  apply Matrix.ext
  intro i j
  apply ContinuousLinearMap.ext
  intro f
  change hilbertMatrixOperator M (lp.single 2 j f) i = M i j f
  simp [lp.single_apply, Pi.single_apply, apply_ite]

omit [CompleteSpace E] in
@[simp] theorem hilbertMatrixOperator_matrix (T : HilbertMatrixSpace N E →L[ℂ] HilbertMatrixSpace N E) :
    hilbertMatrixOperator (hilbertOperatorMatrix T) = T := by
  classical
  apply lp.ext_continuousLinearMap (ENNReal.ofNat_ne_top (n := 2))
  intro j
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext i
  simp [hilbertOperatorMatrix, lp.single_apply, Pi.single_apply, lp.evalCLM, apply_ite]

omit [CompleteSpace E] in
/-- The inner product of an actual block operator is the literal finite matrix contraction. -/
theorem hilbertMatrixOperator_inner (M : Matrix N N (E →L[ℂ] E))
    (f g : HilbertMatrixSpace N E) :
    inner ℂ (hilbertMatrixOperator M f) g = ∑ i, ∑ j, inner ℂ (M i j (f j)) (g i) := by
  rw [lp.inner_eq_tsum, tsum_fintype]
  simp [hilbertMatrixOperator_apply, sum_inner]

omit [CompleteSpace E] in
/-- Matrix multiplication is genuine operator composition on the complete Hilbert sum. -/
theorem hilbertMatrixOperator_mul (M P : Matrix N N (E →L[ℂ] E)) :
    hilbertMatrixOperator (M * P) = hilbertMatrixOperator M * hilbertMatrixOperator P := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext i
  simp only [mul_apply_eq_comp, hilbertMatrixOperator_apply, Matrix.mul_apply,
    sum_apply, mul_apply_eq_comp, map_sum]
  exact Finset.sum_comm

/-- Conjugate transpose is the genuine Hilbert adjoint in the block realization. -/
theorem hilbertMatrixOperator_star (M : Matrix N N (E →L[ℂ] E)) :
    hilbertMatrixOperator (star M) = star (hilbertMatrixOperator M) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f g
  rw [hilbertMatrixOperator_inner, lp.inner_eq_tsum, tsum_fintype]
  simp only [Matrix.star_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left, hilbertMatrixOperator_apply, inner_sum]
  exact Finset.sum_comm

/-- Genuine star-algebra equivalence: canonical C-star matrices are all bounded
operators on the finite complete Hilbert direct sum, including the zero-size case. -/
def hilbertMatrixStarAlgEquiv : CStarMatrix N N (E →L[ℂ] E) ≃⋆ₐ[ℂ]
    (HilbertMatrixSpace N E →L[ℂ] HilbertMatrixSpace N E) where
  toFun M := hilbertMatrixOperator (CStarMatrix.ofMatrix.symm M)
  invFun T := CStarMatrix.ofMatrix (hilbertOperatorMatrix T)
  left_inv M := by change CStarMatrix.ofMatrix (hilbertOperatorMatrix
      (hilbertMatrixOperator (CStarMatrix.ofMatrix.symm M))) = M; simp
  right_inv T := hilbertMatrixOperator_matrix T
  map_mul' M P := hilbertMatrixOperator_mul _ _
  map_add' M P := by
    apply ContinuousLinearMap.ext
    intro f
    apply lp.ext
    funext i
    simp [hilbertMatrixOperator_apply, Finset.sum_add_distrib]
  map_smul' c M := by
    apply ContinuousLinearMap.ext
    intro f
    apply lp.ext
    funext i
    simp [hilbertMatrixOperator_apply, Finset.smul_sum]
  map_star' M := hilbertMatrixOperator_star _

/-- The block realization preserves the entire canonical positive cone. -/
theorem hilbertMatrixStarAlgEquiv_nonneg (M : CStarMatrix N N (E →L[ℂ] E)) (hM : 0 ≤ M) :
    0 ≤ (hilbertMatrixStarAlgEquiv (N := N) (E := E)) M := map_nonneg (hilbertMatrixStarAlgEquiv (N := N) (E := E)) hM

/-- Its genuine inverse proves reflection of the entire positive cone. -/
theorem hilbertMatrixStarAlgEquiv_nonneg_iff (M : CStarMatrix N N (E →L[ℂ] E)) :
    0 ≤ (hilbertMatrixStarAlgEquiv (N := N) (E := E)) M ↔ 0 ≤ M := by
  constructor
  · intro h
    simpa only [StarAlgEquiv.symm_apply_apply] using map_nonneg (hilbertMatrixStarAlgEquiv (N := N) (E := E)).symm h
  · exact hilbertMatrixStarAlgEquiv_nonneg M

end Blocks
end FreeProbability.Fock

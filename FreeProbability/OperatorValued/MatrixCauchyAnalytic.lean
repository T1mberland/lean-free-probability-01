import FreeProbability.OperatorValued.MatrixCauchyPhysical

/-! # Analyticity and decay of the actual affine matrix Cauchy transform

The continuous linear map below takes values in the ELEMENTWISE supremum norm
on ordinary matrices. Its bound does not assert contractivity for the matrix
operator norm or the C-star matrix norm.
-/

noncomputable section
open scoped Classical Topology Matrix.Norms.Elementwise
namespace FreeProbability.Fock

variable {I n : Type*} [Fintype I] [Fintype n] [DecidableEq n]
local instance : PartialOrder (WordSpace I →L[ℂ] WordSpace I) := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing (WordSpace I →L[ℂ] WordSpace I) :=
  CStarAlgebra.spectralOrderedRing _

/-- Actual entrywise vacuum averaging, continuous from the genuine C-star matrix
norm into the explicitly chosen elementwise supremum matrix norm. -/
def matrixVacuumContinuousExpectation :
    CStarMatrix n n (WordSpace I →L[ℂ] WordSpace I) →L[ℂ] Matrix n n ℂ :=
  ((vacuumState I).expectation.mapMatrix.comp
    (CStarMatrix.ofMatrixₗ (R := ℂ)).symm.toLinearMap).mkContinuous 1 (by
      intro T
      change ‖matrixExpectation (vacuumState I).toProbabilitySpace (CStarMatrix.ofMatrix.symm T)‖ ≤ 1 * ‖T‖
      rw [one_mul, Matrix.norm_le_iff (norm_nonneg T)]
      intro r c
      exact (norm_vacuumExpectation_le (T r c)).trans CStarMatrix.norm_entry_le_norm)

omit [Fintype I] [DecidableEq n] in
@[simp] theorem matrixVacuumContinuousExpectation_apply
    (T : CStarMatrix n n (WordSpace I →L[ℂ] WordSpace I)) :
    matrixVacuumContinuousExpectation T =
      matrixExpectation (vacuumState I).toProbabilitySpace (CStarMatrix.ofMatrix.symm T) := rfl

omit [Fintype I] [DecidableEq n] in
/-- Every entry is bounded by the genuine C-star operator-matrix norm. -/
theorem matrixVacuumContinuousExpectation_entry_norm_le
    (T : CStarMatrix n n (WordSpace I →L[ℂ] WordSpace I)) (r c : n) :
    ‖matrixVacuumContinuousExpectation T r c‖ ≤ ‖T‖ :=
  (norm_vacuumExpectation_le (T r c)).trans CStarMatrix.norm_entry_le_norm

/-- The derivative averages the negative square of the actual matrix resolvent. -/
theorem operatorMatrixPencilCauchy_hasDerivAt (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ) (z : ℂ)
    (hz : z ∈ resolventSet ℂ (operatorMatrixPencil C₀ C)) :
    HasDerivAt (operatorMatrixPencilCauchy C₀ C)
      (-matrixExpectation (vacuumState I).toProbabilitySpace
        (CStarMatrix.ofMatrix.symm (resolvent (operatorMatrixPencil C₀ C) z) *
          CStarMatrix.ofMatrix.symm (resolvent (operatorMatrixPencil C₀ C) z))) z := by
  have h := matrixVacuumContinuousExpectation.hasFDerivAt.comp_hasDerivAt z
    (spectrum.hasDerivAt_resolvent_const_left hz)
  rw [pow_two] at h
  have hneg : matrixVacuumContinuousExpectation
      (-(resolvent (operatorMatrixPencil C₀ C) z * resolvent (operatorMatrixPencil C₀ C) z)) =
      -matrixExpectation (vacuumState I).toProbabilitySpace
        (CStarMatrix.ofMatrix.symm (resolvent (operatorMatrixPencil C₀ C) z) *
          CStarMatrix.ofMatrix.symm (resolvent (operatorMatrixPencil C₀ C) z)) := by
    rw [map_neg, matrixVacuumContinuousExpectation_apply]
    rfl
  convert h using 1
  all_goals first | rfl | exact hneg.symm

/-- Actual matrix Cauchy transforms are analytic on their true open resolvent domain. -/
theorem operatorMatrixPencilCauchy_analyticOnNhd (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ) :
    AnalyticOnNhd ℂ (operatorMatrixPencilCauchy C₀ C) (resolventSet ℂ (operatorMatrixPencil C₀ C)) := by
  apply DifferentiableOn.analyticOnNhd _ (spectrum.isOpen_resolventSet _)
  intro z hz
  exact (operatorMatrixPencilCauchy_hasDerivAt C₀ C z hz).differentiableAt.differentiableWithinAt

/-- The actual matrix Cauchy transform tends to zero as the argument escapes
bounded sets. This uses the true inverse, not a formal expansion. -/
theorem operatorMatrixPencilCauchy_tendsto_zero (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ) :
    Filter.Tendsto (operatorMatrixPencilCauchy C₀ C) (Bornology.cobounded ℂ) (𝓝 0) := by
  have h := matrixVacuumContinuousExpectation.continuous.tendsto 0 |>.comp
    (spectrum.resolvent_tendsto_cobounded (𝕜 := ℂ) (operatorMatrixPencil C₀ C))
  simpa only [Function.comp_def, matrixVacuumContinuousExpectation_apply,
    operatorMatrixPencilCauchy, map_zero] using! h

end FreeProbability.Fock

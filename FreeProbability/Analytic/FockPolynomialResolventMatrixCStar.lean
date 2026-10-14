import FreeProbability.Analytic.FockPolynomialResolventCStar
import FreeProbability.Analytic.FockPolynomialResolventMatrix
import FreeProbability.OperatorValued.MatrixExpectation

/-!
# Intrinsic matrix polynomial resolvent IBP in the faithful tracial C-star model

The polynomial matrix and its resolvent belong to the full matrix algebra over
the actual closed C-star algebra. Inclusion preserves the genuine matrix inverse
at every intrinsic invertibility point. No converse domain inclusion is assumed.
-/

noncomputable section
open scoped Classical

namespace FreeProbability.Fock

variable {I N : Type*} [Fintype N] [DecidableEq N]

/-- The actual entrywise algebra inclusion of the closed C-star matrix algebra. -/
def polynomialMatrixInclusion :
    Matrix N N (closedSemicircularAlgebra I) →ₐ[ℂ]
      Matrix N N (WordSpace I →L[ℂ] WordSpace I) :=
  (closedSemicircularAlgebra I).subtype.toAlgHom.mapMatrix

@[simp] theorem polynomialMatrixInclusion_apply
    (X : Matrix N N (closedSemicircularAlgebra I)) (r c : N) :
    polynomialMatrixInclusion X r c = (closedSemicircularAlgebra I).subtype.toAlgHom (X r c) := rfl

/-- The matrix polynomial evaluates to the same actual operators under inclusion. -/
theorem polynomialMatrixInclusion_evaluate (P : Matrix N N (WordPolynomial ℂ I)) :
    polynomialMatrixInclusion (matrixPolynomialEvaluate closedSemicircular P) =
      matrixPolynomialEvaluate semicircular P := by
  apply Matrix.ext
  intro r c
  exact coe_evaluate_closedSemicircular (P r c)

/-- Every intrinsic matrix resolvent point gives a genuine bounded-operator matrix inverse. -/
theorem polynomialMatrix_resolventSet_maps (P : Matrix N N (WordPolynomial ℂ I)) (z : ℂ)
    (hz : z ∈ resolventSet ℂ (matrixPolynomialEvaluate closedSemicircular P)) :
    z ∈ resolventSet ℂ (matrixPolynomialEvaluate semicircular P) := by
  have h := hz.map (polynomialMatrixInclusion (I := I) (N := N)).toMonoidHom
  change IsUnit (polynomialMatrixInclusion
    (algebraMap ℂ (Matrix N N (closedSemicircularAlgebra I)) z -
      matrixPolynomialEvaluate closedSemicircular P)) at h
  simp only [map_sub, AlgHom.commutes, polynomialMatrixInclusion_evaluate] at h
  change IsUnit (algebraMap ℂ (Matrix N N (WordSpace I →L[ℂ] WordSpace I)) z -
    matrixPolynomialEvaluate semicircular P)
  exact h

/-- The actual intrinsic full matrix inverse is preserved by the algebra inclusion. -/
theorem polynomialMatrix_resolvent_coe (P : Matrix N N (WordPolynomial ℂ I)) (z : ℂ)
    (hz : z ∈ resolventSet ℂ (matrixPolynomialEvaluate closedSemicircular P)) :
    polynomialMatrixInclusion (resolvent (matrixPolynomialEvaluate closedSemicircular P) z) =
      resolvent (matrixPolynomialEvaluate semicircular P) z := by
  have h := algHom_map_ringInverse_of_isUnit
    (polynomialMatrixInclusion (I := I) (N := N)) hz
  simpa only [map_sub, AlgHom.commutes, polynomialMatrixInclusion_evaluate, resolvent] using h

/-- Each entry is transported from the actual full matrix resolvent, rather than inverted separately. -/
theorem polynomialMatrix_resolvent_entry_coe (P : Matrix N N (WordPolynomial ℂ I)) (z : ℂ)
    (hz : z ∈ resolventSet ℂ (matrixPolynomialEvaluate closedSemicircular P)) (r c : N) :
    (closedSemicircularAlgebra I).subtype.toAlgHom
      ((resolvent (matrixPolynomialEvaluate closedSemicircular P) z) r c) =
      (resolvent (matrixPolynomialEvaluate semicircular P) z) r c :=
  congrArg (fun X => X r c) (polynomialMatrix_resolvent_coe P z hz)

/-- The actual tensor contraction using the intrinsic amplified faithful tracial state. -/
def closedMatrixPolynomialTensorContraction
    (L R : Matrix N N (closedSemicircularAlgebra I))
    (Z : Matrix N N (PolynomialTensor ℂ I)) (r c : N) : ℂ :=
  ∑ k, ∑ l, closedSandwichPolynomialExpectation (L r k) (R l c) (Z k l)

/-- Full-domain intrinsic matrix polynomial resolvent IBP with the actual `id_M ⊗ τ` state. -/
theorem closedGeneratedVacuumState_matrixPolynomial_resolvent_integrationByParts
    (i : I) (P : Matrix N N (WordPolynomial ℂ I)) (z : ℂ)
    (hz : z ∈ resolventSet ℂ (matrixPolynomialEvaluate closedSemicircular P)) (r c : N) :
    matrixExpectation (closedGeneratedVacuumState I).toProbabilitySpace
      (Matrix.diagonal (fun _ : N => closedSemicircular i) *
        resolvent (matrixPolynomialEvaluate closedSemicircular P) z) r c =
      closedMatrixPolynomialTensorContraction
        (resolvent (matrixPolynomialEvaluate closedSemicircular P) z)
        (resolvent (matrixPolynomialEvaluate closedSemicircular P) z)
        (matrixFreeDifferenceQuotient i P) r c := by
  simp only [matrixExpectation_apply, Matrix.diagonal_mul]
  change vacuumExpectation ((closedSemicircularAlgebra I).subtype.toAlgHom
    (closedSemicircular i * (resolvent (matrixPolynomialEvaluate closedSemicircular P) z) r c)) = _
  rw [map_mul, polynomialMatrix_resolvent_entry_coe P z hz r c]
  simp only [closedMatrixPolynomialTensorContraction, closedSandwichPolynomialExpectation_eq]
  change vacuumExpectation (semicircular i * (resolvent (matrixPolynomialEvaluate semicircular P) z) r c) =
    ∑ k, ∑ l, sandwichPolynomialExpectation
      ((closedSemicircularAlgebra I).subtype.toAlgHom
        ((resolvent (matrixPolynomialEvaluate closedSemicircular P) z) r k))
      ((closedSemicircularAlgebra I).subtype.toAlgHom
        ((resolvent (matrixPolynomialEvaluate closedSemicircular P) z) l c))
      (matrixFreeDifferenceQuotient i P k l)
  simp_rw [polynomialMatrix_resolvent_entry_coe P z hz]
  simpa only [Matrix.map_apply, Matrix.diagonal_mul, matrixExponentialTensorContraction] using
    vacuumState_matrix_polynomial_resolvent_integrationByParts i P z
      (polynomialMatrix_resolventSet_maps P z hz) r c

end FreeProbability.Fock

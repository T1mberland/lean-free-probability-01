import FreeProbability.OperatorValued.MatrixMomentRecursion

/-! # Actual moment recursion for finite affine semicircular matrix pencils -/

noncomputable section
open scoped Classical
namespace FreeProbability

variable {A n I : Type*} [Ring A] [Algebra ℂ A] [Fintype n] [DecidableEq n]

@[simp] theorem matrixPolynomialEvaluate_scalarMatrixEmbedding
    (a : I → A) (C : Matrix n n ℂ) :
    matrixPolynomialEvaluate a (scalarMatrixEmbedding (A := WordPolynomial ℂ I) C) = scalarMatrixEmbedding C := by
  ext r c
  exact (evaluate a).commutes _

@[simp] theorem matrixFreeDifferenceQuotient_scalarMatrixEmbedding
    (i : I) (C : Matrix n n ℂ) :
    matrixFreeDifferenceQuotient (𝕜 := ℂ) i (scalarMatrixEmbedding C) = 0 := by
  ext r c
  change freeDifferenceQuotient i (algebraMap ℂ (WordPolynomial ℂ I) (C r c)) = 0
  rw [Algebra.algebraMap_eq_smul_one, map_smul, freeDifferenceQuotient_one, smul_zero]

omit [Fintype n] [DecidableEq n] in
theorem matrixPolynomialEvaluate_add (a : I → A)
    (P Q : Matrix n n (WordPolynomial ℂ I)) :
    matrixPolynomialEvaluate a (P + Q) = matrixPolynomialEvaluate a P + matrixPolynomialEvaluate a Q := by
  ext r c
  exact map_add (evaluate a) (P r c) (Q r c)

omit [Fintype n] [DecidableEq n] in
theorem matrixFreeDifferenceQuotient_add (i : I)
    (P Q : Matrix n n (WordPolynomial ℂ I)) :
    matrixFreeDifferenceQuotient i (P + Q) = matrixFreeDifferenceQuotient i P + matrixFreeDifferenceQuotient i Q := by
  ext r c
  exact map_add (freeDifferenceQuotient i) (P r c) (Q r c)

namespace Fock
variable [Fintype I]

/-- The true powers of the affine pencil, averaged in the actual vacuum state. -/
def closedMatrixPencilMoment (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ) (k : ℕ) : Matrix n n ℂ :=
  matrixExpectation (closedGeneratedVacuumState I).toProbabilitySpace (closedMatrixPencil C₀ C ^ k)

set_option maxHeartbeats 800000 in
/-- Deterministic drift and covariance give the actual ordered moment recursion
for the affine pencil, without commuting-coefficient assumptions. -/
theorem closedMatrixPencilMoment_recursion (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ) (k : ℕ) :
    closedMatrixPencilMoment C₀ C (k + 1) = C₀ * closedMatrixPencilMoment C₀ C k +
      ∑ j ∈ Finset.range k, matrixCovariance C (closedMatrixPencilMoment C₀ C j) *
        closedMatrixPencilMoment C₀ C (k - 1 - j) := by
  let P : Matrix n n (WordPolynomial ℂ I) := scalarMatrixEmbedding C₀ + matrixLinearPolynomial C
  have he : matrixPolynomialEvaluate closedSemicircular P = closedMatrixPencil C₀ C := by
    dsimp only [P]
    rw [matrixPolynomialEvaluate_add, matrixPolynomialEvaluate_scalarMatrixEmbedding,
      matrixPolynomialEvaluate_linearPolynomial]
    rfl
  have hp (m : ℕ) : matrixPolynomialEvaluate closedSemicircular (P ^ m) = closedMatrixPencil C₀ C ^ m :=
    by rw [matrixPolynomialEvaluate_pow, he]
  have hd (i : I) : matrixFreeDifferenceQuotient i P = matrixConstantTensor (C i) := by
    dsimp only [P]
    rw [matrixFreeDifferenceQuotient_add, matrixFreeDifferenceQuotient_scalarMatrixEmbedding,
      matrixFreeDifferenceQuotient_linearPolynomial, zero_add]
  unfold closedMatrixPencilMoment
  rw [pow_succ', closedMatrixPencil, add_mul, map_add, matrixExpectation_mul_left]
  congr 1
  change matrixExpectation (closedGeneratedVacuumState I).toProbabilitySpace
    (closedMatrixSemicircular C * closedMatrixPencil C₀ C ^ k) = _
  rw [← hp k, closedMatrixSemicircular_polynomial_integrationByParts]
  simp only [matrixFreeDifferenceQuotient_pow, hd, matrixTensorPolynomialExpectation_sum,
    matrixTensorPolynomialExpectation_cut, hp, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [matrixCovariance_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [mul_assoc, closedMatrixPencil]

@[simp] theorem closedMatrixPencilMoment_zero (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ) :
    closedMatrixPencilMoment C₀ C 0 = 1 := by
  unfold closedMatrixPencilMoment
  rw [pow_zero]
  ext r c
  simp [matrixExpectation, Matrix.one_apply, apply_ite]

@[simp] theorem closedMatrixPencilMoment_one (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ) :
    closedMatrixPencilMoment C₀ C 1 = C₀ := by
  simpa using closedMatrixPencilMoment_recursion C₀ C 0

end Fock
end FreeProbability

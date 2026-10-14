import FreeProbability.OperatorValued.MatrixPolynomialExpectation
import FreeProbability.OperatorValued.MatrixSemicircularModel

/-! # Covariance moment recursion in the actual finite matrix Fock model -/

noncomputable section
open scoped Classical
namespace FreeProbability

variable {A n I : Type*} [Ring A] [Algebra ℂ A]

/-- Entrywise tensor expectation respects arbitrary finite sums of tensor matrices. -/
theorem matrixTensorPolynomialExpectation_sum {α : Type*} (φ : ProbabilitySpace ℂ A)
    (a : I → A) (S : Finset α) (Z : α → Matrix n n (PolynomialTensor ℂ I)) :
    matrixTensorPolynomialExpectation φ a (∑ j ∈ S, Z j) =
      ∑ j ∈ S, matrixTensorPolynomialExpectation φ a (Z j) := by
  ext r c
  simp [matrixTensorPolynomialExpectation, Matrix.sum_apply]

namespace Fock
variable [Fintype I] [Fintype n] [DecidableEq n]

/-- Actual matrix moments, using the genuine vacuum state and operator powers. -/
def closedMatrixMoment (C : I → Matrix n n ℂ) (k : ℕ) : Matrix n n ℂ :=
  matrixExpectation (closedGeneratedVacuumState I).toProbabilitySpace
    (closedMatrixSemicircular C ^ k)

/-- Matrix coefficient integration by parts in the genuine closed Fock model. -/
theorem closedMatrixSemicircular_polynomial_integrationByParts
    (C : I → Matrix n n ℂ) (P : Matrix n n (WordPolynomial ℂ I)) :
    matrixExpectation (closedGeneratedVacuumState I).toProbabilitySpace
      (closedMatrixSemicircular C * matrixPolynomialEvaluate closedSemicircular P) =
      ∑ i, C i * matrixTensorPolynomialExpectation
        (closedGeneratedVacuumState I).toProbabilitySpace closedSemicircular
        (matrixFreeDifferenceQuotient i P) := by
  rw [closedMatrixSemicircular, matrixLinearCombination_eq_sum, Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_assoc, matrixExpectation_mul_left]
  congr 1
  exact closedGeneratedVacuumState_matrixPolynomial_integrationByParts i P

/-- Every actual moment satisfies the covariance recursion, with the covariance
acting on the prefix moment and the suffix multiplied on its right. -/
theorem closedMatrixMoment_recursion (C : I → Matrix n n ℂ) (k : ℕ) :
    closedMatrixMoment C (k + 1) =
      ∑ j ∈ Finset.range k, matrixCovariance C (closedMatrixMoment C j) *
        closedMatrixMoment C (k - 1 - j) := by
  have he : matrixPolynomialEvaluate closedSemicircular (matrixLinearPolynomial C) =
      closedMatrixSemicircular C := matrixPolynomialEvaluate_linearPolynomial _ C
  have hp (m : ℕ) : matrixPolynomialEvaluate closedSemicircular (matrixLinearPolynomial C ^ m) =
      closedMatrixSemicircular C ^ m := by rw [matrixPolynomialEvaluate_pow, he]
  unfold closedMatrixMoment
  rw [pow_succ', ← hp k, closedMatrixSemicircular_polynomial_integrationByParts]
  simp only [matrixFreeDifferenceQuotient_pow, matrixFreeDifferenceQuotient_linearPolynomial,
    matrixTensorPolynomialExpectation_sum, matrixTensorPolynomialExpectation_cut, hp,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [matrixCovariance_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [mul_assoc]

@[simp] theorem closedMatrixMoment_zero (C : I → Matrix n n ℂ) :
    closedMatrixMoment C 0 = 1 := by
  unfold closedMatrixMoment
  rw [pow_zero]
  ext r c
  simp [matrixExpectation, Matrix.one_apply, apply_ite]

@[simp] theorem closedMatrixMoment_one (C : I → Matrix n n ℂ) :
    closedMatrixMoment C 1 = 0 := by
  simpa using closedMatrixMoment_recursion C 0

end Fock
end FreeProbability

import FreeProbability.Fock.PolynomialIntegrationByParts
import Mathlib.Data.Matrix.Mul

/-!
# Matrix-valued polynomial free integration by parts

Polynomial evaluation, differentiation and tensor expectation are amplified
entrywise. Expectation is used only as a linear map. The semicircular scalar
matrix acts by actual matrix multiplication, including arbitrary matrix
coefficients. No analytic or norm-convergence extension is asserted.
-/

noncomputable section
open scoped Classical
namespace FreeProbability

variable {𝕜 A I N M : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]

def matrixPolynomialEvaluate (a : I → A) (P : Matrix N M (WordPolynomial 𝕜 I)) : Matrix N M A :=
  fun r c => evaluate a (P r c)

def matrixFreeDifferenceQuotient (i : I) (P : Matrix N M (WordPolynomial 𝕜 I)) :
    Matrix N M (PolynomialTensor 𝕜 I) := fun r c => freeDifferenceQuotient i (P r c)

def matrixTensorPolynomialExpectation (φ : ProbabilitySpace 𝕜 A) (a : I → A)
    (Z : Matrix N M (PolynomialTensor 𝕜 I)) : Matrix N M 𝕜 :=
  fun r c => tensorPolynomialExpectation φ a (Z r c)

/-- Matrix differentiation obeys the amplified tensor bimodule Leibniz rule. -/
theorem matrixFreeDifferenceQuotient_mul [Fintype N]
    (i : I) (P Q : Matrix N N (WordPolynomial 𝕜 I)) (r c : N) :
    matrixFreeDifferenceQuotient i (P * Q) r c =
      ∑ k, tensorLeft (P r k) (matrixFreeDifferenceQuotient i Q k c) +
        ∑ k, tensorRight (Q k c) (matrixFreeDifferenceQuotient i P r k) := by
  simp only [matrixFreeDifferenceQuotient, Matrix.mul_apply, map_sum,
    freeDifferenceQuotient_mul, Finset.sum_add_distrib]

namespace Fock

/-- Genuine `id_M ⊗ τ` integration by parts for arbitrary rectangular matrix-valued polynomials. -/
theorem closedGeneratedVacuumState_matrixPolynomial_integrationByParts
    [Fintype N] [DecidableEq N] (i : I) (P : Matrix N M (WordPolynomial ℂ I)) :
    ((Matrix.diagonal (fun _ : N => closedSemicircular i)) *
        matrixPolynomialEvaluate closedSemicircular P).map
      (closedGeneratedVacuumState I).expectation =
      matrixTensorPolynomialExpectation (closedGeneratedVacuumState I).toProbabilitySpace
        closedSemicircular (matrixFreeDifferenceQuotient i P) := by
  ext r c
  simp only [Matrix.map_apply, Matrix.diagonal_mul, matrixPolynomialEvaluate,
    matrixTensorPolynomialExpectation, matrixFreeDifferenceQuotient]
  exact closedGeneratedVacuumState_polynomial_integrationByParts i (P r c)

end Fock
end FreeProbability

import FreeProbability.Analytic.FockPolynomialResolvent
import FreeProbability.Analytic.FockExponentialMatrix

/-!
# Actual matrix polynomial resolvent integration by parts

The inverse is taken in the full finite-matrix algebra, at every point of the
actual matrix polynomial's resolvent set. Both intermediate matrix indices of
the tensor derivative are retained. No entrywise inverse or exterior expansion
is used.
-/

noncomputable section
open scoped Classical

namespace FreeProbability

/-- The ordered resolvent commutator in any complex algebra, on its entire invertibility domain. -/
theorem commutator_resolvent {A : Type*} [Ring A] [Algebra ℂ A]
    (C a : A) (z : ℂ) (hz : z ∈ resolventSet ℂ a) :
    C * resolvent a z - resolvent a z * C =
      resolvent a z * (C * a - a * C) * resolvent a z := by
  have h := commutator_inverse_unit C hz.unit
  rw [← spectrum.resolvent_eq hz, hz.unit_spec] at h
  have hb : (algebraMap ℂ A z - a) * C - C * (algebraMap ℂ A z - a) = C * a - a * C := by
    simp only [sub_mul, mul_sub, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    abel
  rwa [hb] at h

namespace Fock

variable {I N : Type*} [Fintype N] [DecidableEq N]

/-- Actual rank-one insertion of every entry of a matrix polynomial tensor. -/
def matrixPolynomialRankOneInsertion (Z : Matrix N N (PolynomialTensor ℂ I)) :
    Matrix N N (WordSpace I →L[ℂ] WordSpace I) := fun r c => polynomialRankOneInsertion (Z r c)

omit [DecidableEq N] in
/-- The actual amplified vacuum state contracts a matrix rank-one sandwich with both indices. -/
theorem matrix_vacuum_rankOne_sandwich
    (L R : Matrix N N (WordSpace I →L[ℂ] WordSpace I))
    (Z : Matrix N N (PolynomialTensor ℂ I)) (r c : N) :
    vacuumExpectation ((L * matrixPolynomialRankOneInsertion Z * R) r c) =
      matrixExponentialTensorContraction L R Z r c := by
  change vacuumLinear ((L * matrixPolynomialRankOneInsertion Z * R) r c) = _
  simp only [Matrix.mul_apply]
  simp only [matrixPolynomialRankOneInsertion, Finset.sum_mul, map_sum]
  change (∑ l, ∑ k, vacuumExpectation
    (L r k * polynomialRankOneInsertion (Z k l) * R l c)) = _
  simp_rw [vacuumExpectation_sandwichRankOne]
  rw [Finset.sum_comm]
  rfl

/-- Exact matrix polynomial inverse boundary derivative at every actual matrix resolvent point. -/
theorem matrix_polynomial_resolvent_commutator
    (i : I) (P : Matrix N N (WordPolynomial ℂ I)) (z : ℂ)
    (hz : z ∈ resolventSet ℂ (matrixPolynomialEvaluate semicircular P)) :
    Matrix.diagonal (fun _ : N => rightAnnihilation i) *
        resolvent (matrixPolynomialEvaluate semicircular P) z -
      resolvent (matrixPolynomialEvaluate semicircular P) z *
        Matrix.diagonal (fun _ : N => rightAnnihilation i) =
      resolvent (matrixPolynomialEvaluate semicircular P) z *
        matrixPolynomialRankOneInsertion (matrixFreeDifferenceQuotient i P) *
          resolvent (matrixPolynomialEvaluate semicircular P) z := by
  rw [commutator_resolvent _ _ z hz]
  have hb := matrix_polynomial_commutator i P (1 : ℂ)
  simp only [one_smul] at hb
  rw [hb]
  rfl

/-- Genuine `id_M ⊗ τ` resolvent IBP for arbitrary square matrix-valued polynomials,
using the actual matrix inverse throughout the full resolvent set. -/
theorem vacuumState_matrix_polynomial_resolvent_integrationByParts
    (i : I) (P : Matrix N N (WordPolynomial ℂ I)) (z : ℂ)
    (hz : z ∈ resolventSet ℂ (matrixPolynomialEvaluate semicircular P)) (r c : N) :
    ((Matrix.diagonal (fun _ : N => semicircular i) *
        resolvent (matrixPolynomialEvaluate semicircular P) z).map vacuumExpectation) r c =
      matrixExponentialTensorContraction
        (resolvent (matrixPolynomialEvaluate semicircular P) z)
        (resolvent (matrixPolynomialEvaluate semicircular P) z)
        (matrixFreeDifferenceQuotient i P) r c := by
  have h := congrArg (fun X : Matrix N N (WordSpace I →L[ℂ] WordSpace I) =>
    vacuumExpectation (X r c)) (matrix_polynomial_resolvent_commutator i P z hz)
  simp only [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal] at h
  rw [vacuumExpectation_rightAnnihilation_commutator] at h
  simp only [Matrix.map_apply, Matrix.diagonal_mul]
  exact h.trans (matrix_vacuum_rankOne_sandwich _ _ _ r c)

end Fock
end FreeProbability

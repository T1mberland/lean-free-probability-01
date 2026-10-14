import FreeProbability.OperatorValued.MatrixExpectation
import FreeProbability.OperatorValued.MatrixCovariance
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.BigOperators

/-! # Actual matrix linear combinations of scalar random variables -/

namespace FreeProbability

open Matrix

variable {A n I : Type*} [Ring A] [Algebra ℂ A] [Fintype n] [DecidableEq n] [Fintype I]

/-- An actual matrix over the ambient algebra with scalar matrix coefficients. -/
def matrixLinearCombination (s : I → A) (C : I → Matrix n n ℂ) : Matrix n n A :=
  fun r c => ∑ i, C i r c • s i

/-- The entrywise form agrees with the literal sum of coefficient matrices times
scalar diagonal random variables. -/
theorem matrixLinearCombination_eq_sum (s : I → A) (C : I → Matrix n n ℂ) :
    matrixLinearCombination s C =
      ∑ i, scalarMatrixEmbedding (C i) * Matrix.diagonal (fun _ : n => s i) := by
  classical
  ext r c
  rw [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mul_diagonal]
  exact Algebra.smul_def _ _

omit [Fintype n] [DecidableEq n] in
/-- Matrix expectation of the actual coefficient sum. -/
theorem matrixExpectation_linearCombination (φ : ProbabilitySpace ℂ A)
    (s : I → A) (C : I → Matrix n n ℂ) :
    matrixExpectation φ (matrixLinearCombination s C) = ∑ i, φ.expectation (s i) • C i := by
  classical
  ext r c
  rw [Matrix.sum_apply]
  change φ.expectation (∑ i, C i r c • s i) = ∑ i, φ.expectation (s i) * C i r c
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, smul_eq_mul, mul_comm]

omit [Fintype n] [DecidableEq n] in
/-- Actual centering requires only the scalar first moments to vanish. -/
theorem matrixExpectation_linearCombination_centered (φ : ProbabilitySpace ℂ A)
    (s : I → A) (C : I → Matrix n n ℂ) (hs : ∀ i, φ.expectation (s i) = 0) :
    matrixExpectation φ (matrixLinearCombination s C) = 0 := by
  rw [matrixExpectation_linearCombination]
  simp only [hs, zero_smul, Finset.sum_const_zero]

omit [Fintype n] [DecidableEq n] in
/-- Hermitian matrix coefficients and self-adjoint scalar variables give an
actual self-adjoint matrix, without requiring the matrix coefficients to commute. -/
theorem matrixLinearCombination_isHermitian [StarRing A] [StarModule ℂ A]
    (s : I → A) (C : I → Matrix n n ℂ) (hs : ∀ i, star (s i) = s i)
    (hC : ∀ i, (C i).IsHermitian) : (matrixLinearCombination s C).IsHermitian := by
  classical
  apply IsHermitian.ext
  intro r c
  change star (∑ i, C i c r • s i) = ∑ i, C i r c • s i
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [star_smul, hs, (hC i).apply]

private theorem expectation_two_scaled_variables (φ : ProbabilitySpace ℂ A)
    (c d e : ℂ) (x y : A) :
    φ.expectation ((c • x) * algebraMap ℂ A d * (e • y)) = c * d * e * φ.expectation (x * y) := by
  simp only [smul_mul_assoc, mul_smul_comm, map_smul, smul_eq_mul]
  rw [← Algebra.commutes d x, mul_assoc, ← Algebra.smul_def, map_smul, smul_eq_mul]
  ac_rfl

/-- Covariance of the actual matrix sum is computed from the genuine scalar
second moments, with the noncommuting coefficient order preserved. -/
theorem matrixExpectation_linearCombination_covariance [DecidableEq I] (φ : ProbabilitySpace ℂ A)
    (s : I → A) (C : I → Matrix n n ℂ)
    (hsecond : ∀ i j, φ.expectation (s i * s j) = if i = j then 1 else 0)
    (D : Matrix n n ℂ) :
    matrixExpectation φ (matrixLinearCombination s C * scalarMatrixEmbedding D * matrixLinearCombination s C) =
      matrixCovariance C D := by
  classical
  ext r c
  rw [matrixCovariance_apply, Matrix.sum_apply]
  change φ.expectation (∑ v, (∑ u, (∑ i, C i r u • s i) * algebraMap ℂ A (D u v)) *
      (∑ j, C j v c • s j)) = ∑ i, (C i * D * C i) r c
  simp only [Finset.sum_mul, Finset.mul_sum, map_sum, expectation_two_scaled_variables,
    hsecond, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

end FreeProbability

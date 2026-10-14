import FreeProbability.OperatorValued.MatrixPencilMoments
import FreeProbability.OperatorValued.MatrixFormalDyson

/-! # Formal Dyson identity for the actual affine matrix pencil

This coefficient identity is formal; analytic convergence is separate.
-/

noncomputable section
open scoped Classical
namespace FreeProbability.Fock

variable {n I : Type*} [Fintype n] [DecidableEq n] [Fintype I]

/-- Formal generating series of genuine affine pencil moments. -/
def closedMatrixPencilMomentSeries (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ) :
    PowerSeries (Matrix n n ℂ) := PowerSeries.mk (closedMatrixPencilMoment C₀ C)

@[simp] theorem closedMatrixPencilMomentSeries_coeff (C₀ : Matrix n n ℂ)
    (C : I → Matrix n n ℂ) (k : ℕ) :
    PowerSeries.coeff k (closedMatrixPencilMomentSeries C₀ C) = closedMatrixPencilMoment C₀ C k :=
  PowerSeries.coeff_mk _ _

/-- Actual affine moments satisfy the ordered formal Dyson identity, including
its deterministic drift term and genuine covariance term. -/
theorem closedMatrixPencilMomentSeries_dyson (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ) :
    closedMatrixPencilMomentSeries C₀ C =
      1 + PowerSeries.X * (PowerSeries.C C₀ * closedMatrixPencilMomentSeries C₀ C) +
        PowerSeries.X ^ 2 * (matrixCovarianceSeries C (closedMatrixPencilMomentSeries C₀ C) *
          closedMatrixPencilMomentSeries C₀ C) := by
  apply PowerSeries.ext
  intro k
  cases k with
  | zero => simp
  | succ k =>
    cases k with
    | zero => simp [PowerSeries.coeff_X_pow_mul']
    | succ k =>
      simp only [map_add, PowerSeries.coeff_one, Nat.succ_ne_zero, ite_false, zero_add,
        PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul, closedMatrixPencilMomentSeries_coeff,
        PowerSeries.coeff_X_pow_mul']
      simp only [show 2 ≤ k + 1 + 1 by omega, ite_true, show k + 1 + 1 - 2 = k by omega,
        PowerSeries.coeff_mul, matrixCovarianceSeries_coeff, closedMatrixPencilMomentSeries_coeff]
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simpa using closedMatrixPencilMoment_recursion C₀ C (k + 1)

end FreeProbability.Fock

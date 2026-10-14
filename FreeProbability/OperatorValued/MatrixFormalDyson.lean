import FreeProbability.OperatorValued.MatrixMomentRecursion
import Mathlib.RingTheory.PowerSeries.Basic

/-! # Formal matrix Dyson equation for genuine Fock moments

This is a formal coefficient identity. No analytic convergence or identification
with a matrix resolvent on a complex domain is asserted here.
-/

noncomputable section
open scoped Classical
namespace FreeProbability

variable {n I : Type*} [Fintype n] [DecidableEq n] [Fintype I]

/-- Coefficientwise extension of the actual finite matrix covariance. -/
def matrixCovarianceSeries (C : I → Matrix n n ℂ) (F : PowerSeries (Matrix n n ℂ)) :
    PowerSeries (Matrix n n ℂ) :=
  PowerSeries.mk (fun k => matrixCovariance C (PowerSeries.coeff k F))

@[simp] theorem matrixCovarianceSeries_coeff (C : I → Matrix n n ℂ)
    (F : PowerSeries (Matrix n n ℂ)) (k : ℕ) :
    PowerSeries.coeff k (matrixCovarianceSeries C F) =
      matrixCovariance C (PowerSeries.coeff k F) := PowerSeries.coeff_mk _ _

namespace Fock

/-- Generating series of the actual matrix moments, including its unit term. -/
def closedMatrixMomentSeries (C : I → Matrix n n ℂ) : PowerSeries (Matrix n n ℂ) :=
  PowerSeries.mk (closedMatrixMoment C)

@[simp] theorem closedMatrixMomentSeries_coeff (C : I → Matrix n n ℂ) (k : ℕ) :
    PowerSeries.coeff k (closedMatrixMomentSeries C) = closedMatrixMoment C k :=
  PowerSeries.coeff_mk _ _

/-- The genuine matrix Fock moment series solves the ordered formal Dyson
identity `M = 1 + X² η(M) M`. -/
theorem closedMatrixMomentSeries_dyson (C : I → Matrix n n ℂ) :
    closedMatrixMomentSeries C = 1 + PowerSeries.X ^ 2 *
      (matrixCovarianceSeries C (closedMatrixMomentSeries C) * closedMatrixMomentSeries C) := by
  apply PowerSeries.ext
  intro k
  cases k with
  | zero => simp
  | succ k =>
    cases k with
    | zero => simp [PowerSeries.coeff_X_pow_mul']
    | succ k =>
      simp only [map_add, PowerSeries.coeff_one, Nat.succ_ne_zero, ite_false, zero_add,
        PowerSeries.coeff_X_pow_mul']
      simp only [show 2 ≤ k + 1 + 1 by omega, ite_true, show k + 1 + 1 - 2 = k by omega,
        PowerSeries.coeff_mul, matrixCovarianceSeries_coeff, closedMatrixMomentSeries_coeff]
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simpa using closedMatrixMoment_recursion C (k + 1)

/-- The formal Dyson equation determines every coefficient uniquely; in
particular its solution is the generating series of the actual Fock moments. -/
theorem closedMatrixMomentSeries_unique (C : I → Matrix n n ℂ)
    (F : PowerSeries (Matrix n n ℂ))
    (hF : F = 1 + PowerSeries.X ^ 2 * (matrixCovarianceSeries C F * F)) :
    F = closedMatrixMomentSeries C := by
  have hzero : PowerSeries.coeff 0 F = 1 := by
    simpa using congrArg (PowerSeries.coeff 0) hF
  have hone : PowerSeries.coeff 1 F = 0 := by
    simpa [PowerSeries.coeff_X_pow_mul'] using congrArg (PowerSeries.coeff 1) hF
  have hrec (k : ℕ) : PowerSeries.coeff (k + 2) F =
      ∑ j ∈ Finset.range (k + 1), matrixCovariance C (PowerSeries.coeff j F) *
        PowerSeries.coeff (k - j) F := by
    have h := congrArg (PowerSeries.coeff (k + 2)) hF
    simp only [map_add, PowerSeries.coeff_one, show k + 2 ≠ 0 by omega, ite_false,
      zero_add, PowerSeries.coeff_X_pow_mul', show 2 ≤ k + 2 by omega, ite_true,
      Nat.add_sub_cancel] at h
    simp only [PowerSeries.coeff_mul, matrixCovarianceSeries_coeff] at h
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
    exact h
  apply PowerSeries.ext
  intro k
  simp only [closedMatrixMomentSeries_coeff]
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simpa using hzero
    | succ k =>
      cases k with
      | zero => simpa using hone
      | succ k =>
        rw [show k + 1 + 1 = k + 2 by omega, hrec,
          show k + 2 = (k + 1) + 1 by omega, closedMatrixMoment_recursion]
        simp only [Nat.add_sub_cancel]
        apply Finset.sum_congr rfl
        intro j hj
        have hjk := Finset.mem_range.mp hj
        rw [ih j (by omega), ih (k - j) (by omega)]

end Fock
end FreeProbability

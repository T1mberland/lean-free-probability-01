import FreeProbability.Analytic.ProjectionProductPicardFormal
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! # Genuine evaluation of absolutely convergent scalar power series -/

noncomputable section
namespace FreeProbability

/-- Actual scalar series evaluation, with convergence proved separately. -/
def scalarPowerSeriesSum (P : PowerSeries ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, PowerSeries.coeff n P * z ^ n

/-- Absolute convergence of the genuine scalar series at a supplied point. -/
def scalarPowerSeriesSummable (P : PowerSeries ℂ) (z : ℂ) : Prop :=
  Summable (fun n : ℕ => ‖PowerSeries.coeff n P * z ^ n‖)

private theorem powerSeries_mul_term (P Q : PowerSeries ℂ) (z : ℂ) (n : ℕ) :
    PowerSeries.coeff n (P * Q) * z ^ n =
      ∑ ij ∈ Finset.antidiagonal n,
        (PowerSeries.coeff ij.1 P * z ^ ij.1) * (PowerSeries.coeff ij.2 Q * z ^ ij.2) := by
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have he : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
  rw [← he, pow_add]
  ring

/-- Absolute convergence is preserved by formal multiplication. -/
theorem scalarPowerSeriesSummable_mul (P Q : PowerSeries ℂ) (z : ℂ)
    (hP : scalarPowerSeriesSummable P z) (hQ : scalarPowerSeriesSummable Q z) :
    scalarPowerSeriesSummable (P * Q) z := by
  simpa only [scalarPowerSeriesSummable, powerSeries_mul_term] using
    summable_norm_sum_mul_antidiagonal_of_summable_norm hP hQ

/-- Formal multiplication evaluates to actual multiplication when both
series are absolutely convergent. -/
theorem scalarPowerSeriesSum_mul (P Q : PowerSeries ℂ) (z : ℂ)
    (hP : scalarPowerSeriesSummable P z) (hQ : scalarPowerSeriesSummable Q z) :
    scalarPowerSeriesSum (P * Q) z = scalarPowerSeriesSum P z * scalarPowerSeriesSum Q z := by
  exact (tsum_congr (fun n => powerSeries_mul_term P Q z n)).trans
    (tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hP hQ).symm

theorem scalarPowerSeriesSummable_C (c z : ℂ) : scalarPowerSeriesSummable (PowerSeries.C c) z := by
  change Summable (fun n : ℕ => ‖PowerSeries.coeff n (PowerSeries.C c) * z ^ n‖)
  convert (hasSum_ite_eq 0 ‖c‖).summable using 1
  funext n
  by_cases hn : n = 0 <;> simp [PowerSeries.coeff_C, hn]

@[simp] theorem scalarPowerSeriesSum_C (c z : ℂ) : scalarPowerSeriesSum (PowerSeries.C c) z = c := by
  simp [scalarPowerSeriesSum, PowerSeries.coeff_C]

theorem scalarPowerSeriesSummable_X (z : ℂ) : scalarPowerSeriesSummable PowerSeries.X z := by
  change Summable (fun n : ℕ => ‖PowerSeries.coeff n PowerSeries.X * z ^ n‖)
  convert (hasSum_ite_eq 1 ‖z‖).summable using 1
  funext n
  by_cases hn : n = 1 <;> simp [PowerSeries.coeff_X, hn]

@[simp] theorem scalarPowerSeriesSum_X (z : ℂ) : scalarPowerSeriesSum PowerSeries.X z = z := by
  simp [scalarPowerSeriesSum, PowerSeries.coeff_X]

theorem scalarPowerSeriesSummable_add (P Q : PowerSeries ℂ) (z : ℂ)
    (hP : scalarPowerSeriesSummable P z) (hQ : scalarPowerSeriesSummable Q z) :
    scalarPowerSeriesSummable (P + Q) z := by
  apply (hP.add hQ).of_nonneg_of_le (fun n => norm_nonneg _)
  intro n
  simp only [map_add, add_mul]
  exact norm_add_le _ _

theorem scalarPowerSeriesSum_add (P Q : PowerSeries ℂ) (z : ℂ)
    (hP : scalarPowerSeriesSummable P z) (hQ : scalarPowerSeriesSummable Q z) :
    scalarPowerSeriesSum (P + Q) z = scalarPowerSeriesSum P z + scalarPowerSeriesSum Q z := by
  simp only [scalarPowerSeriesSum, map_add, add_mul]
  exact hP.of_norm.tsum_add hQ.of_norm

theorem scalarPowerSeriesSummable_pow (P : PowerSeries ℂ) (z : ℂ)
    (hP : scalarPowerSeriesSummable P z) (L : ℕ) : scalarPowerSeriesSummable (P ^ L) z := by
  induction L with
  | zero => simpa using scalarPowerSeriesSummable_C 1 z
  | succ L ih => rw [pow_succ]; exact scalarPowerSeriesSummable_mul _ _ z ih hP

theorem scalarPowerSeriesSum_pow (P : PowerSeries ℂ) (z : ℂ)
    (hP : scalarPowerSeriesSummable P z) (L : ℕ) :
    scalarPowerSeriesSum (P ^ L) z = scalarPowerSeriesSum P z ^ L := by
  induction L with
  | zero => simpa using scalarPowerSeriesSum_C 1 z
  | succ L ih => rw [pow_succ, scalarPowerSeriesSum_mul _ _ z
      (scalarPowerSeriesSummable_pow P z hP L) hP, ih, pow_succ]
/-- A formal implicit equation becomes a literal equation of the actual
convergent scalar sum, with all product evaluations justified. -/
theorem scalarPowerSeriesSum_implicit_equation (L : ℕ) (c z : ℂ) (Q : PowerSeries ℂ)
    (hQ : Q = PowerSeries.C c * PowerSeries.X * (1 + Q) ^ L)
    (hs : scalarPowerSeriesSummable Q z) :
    scalarPowerSeriesSum Q z = c * z * (1 + scalarPowerSeriesSum Q z) ^ L := by
  have h1 : scalarPowerSeriesSummable (1 : PowerSeries ℂ) z := by
    simpa using scalarPowerSeriesSummable_C 1 z
  have hadd := scalarPowerSeriesSummable_add 1 Q z h1 hs
  have hpow := scalarPowerSeriesSummable_pow (1 + Q) z hadd L
  have hcx := scalarPowerSeriesSummable_mul (PowerSeries.C c) PowerSeries.X z
    (scalarPowerSeriesSummable_C c z) (scalarPowerSeriesSummable_X z)
  conv_lhs => rw [hQ]
  rw [scalarPowerSeriesSum_mul _ _ z hcx hpow,
    scalarPowerSeriesSum_mul _ _ z (scalarPowerSeriesSummable_C c z) (scalarPowerSeriesSummable_X z),
    scalarPowerSeriesSum_C, scalarPowerSeriesSum_X, scalarPowerSeriesSum_pow _ _ hadd,
    scalarPowerSeriesSum_add _ _ z h1 hs]
  have hone : scalarPowerSeriesSum (1 : PowerSeries ℂ) z = 1 := by
    simpa using scalarPowerSeriesSum_C 1 z
  rw [hone]
end FreeProbability

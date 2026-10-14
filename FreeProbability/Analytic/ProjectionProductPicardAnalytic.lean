import FreeProbability.Analytic.ProjectionProductSeriesEvaluation
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.ChangeOrigin

/-! # Genuine complex analytic sums of the nonnegative Picard coefficients -/

noncomputable section
open scoped Topology ENNReal NNReal
namespace FreeProbability

/-- The complex formal series of the stabilized real Picard coefficients. -/
def halfProjectionComplexSeries (L : ℕ) : PowerSeries ℂ :=
  PowerSeries.map Complex.ofRealHom (halfProjectionPicardSeries L)

@[simp] theorem halfProjectionComplexSeries_coeff (L n : ℕ) :
    PowerSeries.coeff n (halfProjectionComplexSeries L) = (halfProjectionPicardCoefficient L n : ℂ) := by
  simp [halfProjectionComplexSeries]

/-- The complex series satisfies the literal same implicit equation. -/
theorem halfProjectionComplexSeries_equation (L : ℕ) :
    halfProjectionComplexSeries L = PowerSeries.C ((2 : ℂ) ^ L)⁻¹ * PowerSeries.X *
      (1 + halfProjectionComplexSeries L) ^ L := by
  have h := congrArg (PowerSeries.map Complex.ofRealHom) (halfProjectionPicardSeries_equation L)
  simpa [halfProjectionComplexSeries, map_mul, map_add, map_pow] using h

/-- The genuine complex Picard sum. -/
def halfProjectionAnalyticSum (L : ℕ) (z : ℂ) : ℂ :=
  scalarPowerSeriesSum (halfProjectionComplexSeries L) z

/-- The scalar Taylor series corresponding to the genuine complex sum. -/
def halfProjectionTaylorSeries (L : ℕ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n => (halfProjectionPicardCoefficient L n : ℂ))

/-- A scalar supersolution proves actual absolute convergence at every
complex point of bounded modulus. -/
theorem halfProjectionComplexSeries_summable (L : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (r : ℝ) (hr : 0 ≤ r) (hsuper : (t / (2 : ℝ) ^ L) * (1 + r) ^ L ≤ r)
    (z : ℂ) (hz : ‖z‖ ≤ t) : scalarPowerSeriesSummable (halfProjectionComplexSeries L) z := by
  apply (halfProjectionPicardCoefficient_summable L t ht r hr hsuper).of_nonneg_of_le
    (fun n => norm_nonneg _)
  intro n
  simp only [halfProjectionComplexSeries_coeff, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg (halfProjectionPicardCoefficient_nonneg L n)]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hz n)
    (halfProjectionPicardCoefficient_nonneg L n)

/-- The actual complex sum has the same quantitative scalar norm bound. -/
theorem halfProjectionAnalyticSum_norm_le (L : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (r : ℝ) (hr : 0 ≤ r) (hsuper : (t / (2 : ℝ) ^ L) * (1 + r) ^ L ≤ r)
    (z : ℂ) (hz : ‖z‖ ≤ t) : ‖halfProjectionAnalyticSum L z‖ ≤ r := by
  have hs := halfProjectionComplexSeries_summable L t ht r hr hsuper z hz
  calc
    _ ≤ ∑' n : ℕ, ‖PowerSeries.coeff n (halfProjectionComplexSeries L) * z ^ n‖ :=
      norm_tsum_le_tsum_norm hs
    _ ≤ ∑' n : ℕ, halfProjectionPicardCoefficient L n * t ^ n := by
      apply Summable.tsum_le_tsum _ hs (halfProjectionPicardCoefficient_summable L t ht r hr hsuper)
      intro n
      simp only [halfProjectionComplexSeries_coeff, norm_mul, norm_pow, Complex.norm_real,
        Real.norm_of_nonneg (halfProjectionPicardCoefficient_nonneg L n)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hz n)
        (halfProjectionPicardCoefficient_nonneg L n)
    _ ≤ r := halfProjectionPicardCoefficient_tsum_le_supersolution L t ht r hr hsuper

/-- The genuine convergent complex sum satisfies the implicit equation. -/
theorem halfProjectionAnalyticSum_equation (L : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (r : ℝ) (hr : 0 ≤ r) (hsuper : (t / (2 : ℝ) ^ L) * (1 + r) ^ L ≤ r)
    (z : ℂ) (hz : ‖z‖ ≤ t) :
    halfProjectionAnalyticSum L z = ((2 : ℂ) ^ L)⁻¹ * z * (1 + halfProjectionAnalyticSum L z) ^ L :=
  scalarPowerSeriesSum_implicit_equation L _ z _ (halfProjectionComplexSeries_equation L)
    (halfProjectionComplexSeries_summable L t ht r hr hsuper z hz)

/-- Actual coefficient summability supplies the Taylor-series radius bound. -/
theorem le_halfProjectionTaylorSeries_radius (L : ℕ) (t : ℝ≥0)
    (r : ℝ) (hr : 0 ≤ r) (hsuper : ((t : ℝ) / (2 : ℝ) ^ L) * (1 + r) ^ L ≤ r) :
    (t : ℝ≥0∞) ≤ (halfProjectionTaylorSeries L).radius := by
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  simpa only [halfProjectionTaylorSeries, FormalMultilinearSeries.ofScalars_norm,
    Complex.norm_real, Real.norm_of_nonneg (halfProjectionPicardCoefficient_nonneg L _)] using
    halfProjectionPicardCoefficient_summable L t t.coe_nonneg r hr hsuper

/-- The actual complex sum is exactly the sum of its scalar Taylor series. -/
theorem halfProjectionAnalyticSum_eq_taylorSum (L : ℕ) :
    halfProjectionAnalyticSum L = (halfProjectionTaylorSeries L).sum := by
  funext z
  simpa only [halfProjectionAnalyticSum, scalarPowerSeriesSum, halfProjectionComplexSeries_coeff,
    FormalMultilinearSeries.ofScalarsSum, halfProjectionTaylorSeries, smul_eq_mul] using
    (FormalMultilinearSeries.ofScalars_sum_eq
      (fun n => (halfProjectionPicardCoefficient L n : ℂ)) z).symm

/-- A positive scalar supersolution domain yields a genuine analytic
expansion of the constructed sum, without assuming analyticity. -/
theorem halfProjectionAnalyticSum_hasFPowerSeries (L : ℕ) (t : ℝ≥0) (ht : 0 < t)
    (r : ℝ) (hr : 0 ≤ r) (hsuper : ((t : ℝ) / (2 : ℝ) ^ L) * (1 + r) ^ L ≤ r) :
    HasFPowerSeriesOnBall (halfProjectionAnalyticSum L) (halfProjectionTaylorSeries L) 0 t := by
  rw [halfProjectionAnalyticSum_eq_taylorSum]
  have hb := le_halfProjectionTaylorSeries_radius L t r hr hsuper
  have htE : (0 : ℝ≥0∞) < t := by exact_mod_cast ht
  have hp : 0 < (halfProjectionTaylorSeries L).radius := htE.trans_le hb
  exact ((halfProjectionTaylorSeries L).hasFPowerSeriesOnBall hp).mono (by exact_mod_cast ht) hb
@[simp] theorem halfProjectionAnalyticSum_zero (L : ℕ) : halfProjectionAnalyticSum L 0 = 0 := by
  rw [halfProjectionAnalyticSum_eq_taylorSum]
  change FormalMultilinearSeries.ofScalarsSum
    (fun n => (halfProjectionPicardCoefficient L n : ℂ)) 0 = 0
  rw [FormalMultilinearSeries.ofScalarsSum_zero]
  simp [halfProjectionPicardCoefficient, halfProjectionPicardPolynomial]

/-- A concrete uniform half-unit disk provides a proved analytic germ of
the Picard sum for every length, without any supplied convergence premise. -/
theorem halfProjectionAnalyticSum_hasFPowerSeries_half (L : ℕ) :
    HasFPowerSeriesOnBall (halfProjectionAnalyticSum L) (halfProjectionTaylorSeries L) 0 (1 / 2 : ℝ≥0∞) := by
  have hs : (((1 / 2 : ℝ≥0) : ℝ) / (2 : ℝ) ^ L) * (1 + (1 : ℝ)) ^ L ≤ 1 := by
    norm_num only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat, one_add_one_eq_two]
    rw [div_mul_cancel₀ _ (pow_ne_zero L (by norm_num))]
    norm_num
  convert halfProjectionAnalyticSum_hasFPowerSeries L (1 / 2) (by norm_num) 1 (by norm_num) hs using 1
  norm_num

theorem analyticAt_halfProjectionAnalyticSum_zero (L : ℕ) :
    AnalyticAt ℂ (halfProjectionAnalyticSum L) 0 :=
  (halfProjectionAnalyticSum_hasFPowerSeries_half L).analyticAt
end FreeProbability

import FreeProbability.Analytic.ProjectionProductPicardIdentification
import FreeProbability.Analytic.ProjectionProductMomentSupport
import Mathlib.Analysis.Complex.CauchyIntegral

/-! # True actual moment summability from Picard analytic majorants -/

noncomputable section
open scoped Topology NNReal ENNReal
namespace FreeProbability

/-- The analytic reciprocal of the normalized Picard sum. -/
def halfProjectionInverseMomentSum (L : ℕ) (z : ℂ) : ℂ :=
  1 / (1 - halfProjectionAnalyticSum L z)

/-- A Picard supersolution strictly below one makes the actual reciprocal
analytic throughout the corresponding open disk. -/
theorem halfProjectionInverseMomentSum_analyticAt (L : ℕ) (t : ℝ≥0) (ht : 0 < t)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hsuper : ((t : ℝ) / (2 : ℝ) ^ L) * (1 + r) ^ L ≤ r)
    (z : ℂ) (hz : ‖z‖ < t) : AnalyticAt ℂ (halfProjectionInverseMomentSum L) z := by
  have hQ := (halfProjectionAnalyticSum_hasFPowerSeries L t ht r hr hsuper).analyticAt_of_mem
    (by simp only [Metric.mem_eball, edist_zero_right, enorm_lt_coe]; exact_mod_cast hz)
  have hn : 1 - halfProjectionAnalyticSum L z ≠ 0 := by
    intro he
    have hqe : halfProjectionAnalyticSum L z = 1 := (sub_eq_zero.mp he).symm
    have hb := halfProjectionAnalyticSum_norm_le L t t.coe_nonneg r hr hsuper z hz.le
    rw [hqe, norm_one] at hb
    exact (not_le_of_gt hr1) hb
  exact analyticAt_const.div (analyticAt_const.sub hQ) hn

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
namespace StarProbabilitySpace
variable (φ : FreeProbability.StarProbabilitySpace A)

/-- The actual inverse-expectation Taylor series, with the true marginal
power moments as coefficients. -/
def expectationInverseTaylorSeries (a : A) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n => φ.expectation (a ^ n))

/-- Actual Neumann sums supply a genuine analytic expansion with the actual
power moments, without an assumed power-series identification. -/
theorem hasFPowerSeriesAt_expectation_inverse (a : A) :
    HasFPowerSeriesAt (fun z : ℂ => φ.expectation (Ring.inverse (1 - z • a)))
      (φ.expectationInverseTaylorSeries a) 0 := by
  apply hasFPowerSeriesAt_iff.mpr
  have hsmall : ∀ᶠ z : ℂ in 𝓝 0, ‖z‖ * ‖a‖ < 1 :=
    (continuous_norm.mul_const ‖a‖).continuousAt.eventually_lt continuousAt_const (by simp)
  filter_upwards [hsmall] with z hz
  simpa only [expectationInverseTaylorSeries, FormalMultilinearSeries.coeff_ofScalars,
    zero_add, smul_eq_mul] using φ.hasSum_expectation_inverse a z hz

/-- The genuine inverse expectation is locally the analytic reciprocal of
the actual Picard sum for the supplied free half projections. -/
theorem expectation_inverse_eq_picard_reciprocal_eventually
    (hφ : IsTracial φ.toProbabilitySpace) (n : ℕ) {B : Fin (n + 1) → Subalgebra ℂ A}
    (hf : FreelyIndependent φ.toProbabilitySpace B) (p : Fin (n + 1) → A)
    (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, IsStarProjection (p i))
    (hE : ∀ i, φ.expectation (p i) = (1 / 2 : ℂ)) :
    (fun z : ℂ => φ.expectation (Ring.inverse (1 - z • iteratedPositiveProduct (n + 1) p)))
      =ᶠ[𝓝 0] halfProjectionInverseMomentSum (n + 1) := by
  have hden : ∀ᶠ z : ℂ in 𝓝 0, 1 - halfProjectionAnalyticSum (n + 1) z ≠ 0 :=
    (continuousAt_const.sub (analyticAt_halfProjectionAnalyticSum_zero _).continuousAt).eventually_ne (by simp)
  filter_upwards [φ.momentGeneratingFunction_eq_picard_fraction_eventually hφ n hf p hpB hp hE,
    hden] with z hz hd
  have he : φ.expectation (Ring.inverse (1 - z • iteratedPositiveProduct (n + 1) p)) =
      φ.momentGeneratingFunction (iteratedPositiveProduct (n + 1) p) z + 1 := by
    simp [momentGeneratingFunction]
  rw [he, hz, halfProjectionInverseMomentSum]
  field_simp
  ring
/-- The true actual moment Taylor series inherits every smaller disk from
the analytic Picard reciprocal, via Cauchy expansion and kernel-checked
uniqueness of analytic coefficients. -/
theorem expectationInverseTaylorSeries_iteratedHalfProjection_radius_bound
    (hφ : IsTracial φ.toProbabilitySpace) (n : ℕ) {B : Fin (n + 1) → Subalgebra ℂ A}
    (hf : FreelyIndependent φ.toProbabilitySpace B) (p : Fin (n + 1) → A)
    (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, IsStarProjection (p i))
    (hE : ∀ i, φ.expectation (p i) = (1 / 2 : ℂ))
    (t : ℝ≥0) (ht : 0 < t) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hsuper : ((t : ℝ) / (2 : ℝ) ^ (n + 1)) * (1 + r) ^ (n + 1) ≤ r)
    (s : ℝ≥0) (hs : 0 < s) (hst : s < t) :
    (s : ℝ≥0∞) ≤ (φ.expectationInverseTaylorSeries (iteratedPositiveProduct (n + 1) p)).radius := by
  have hd : DifferentiableOn ℂ (halfProjectionInverseMomentSum (n + 1)) (Metric.closedBall 0 s) := by
    intro z hz
    have hzs : ‖z‖ ≤ s := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    exact (halfProjectionInverseMomentSum_analyticAt (n + 1) t ht r hr hr1 hsuper z
      (hzs.trans_lt (by exact_mod_cast hst))).differentiableAt.differentiableWithinAt
  have hlarge := hd.hasFPowerSeriesOnBall hs
  have hseries := (φ.hasFPowerSeriesAt_expectation_inverse (iteratedPositiveProduct (n + 1) p)).eq_formalMultilinearSeries_of_eventually
    hlarge.hasFPowerSeriesAt (φ.expectation_inverse_eq_picard_reciprocal_eventually hφ n hf p hpB hp hE)
  rw [hseries]
  exact hlarge.r_le

/-- A concrete Picard supersolution below one proves TRUE absolute
summability of the actual half-projection moment coefficients throughout
the subcritical disk. No moment-summability premise is assumed. -/
theorem summable_actual_iteratedHalfProjection_moments
    (hφ : IsTracial φ.toProbabilitySpace) (n : ℕ) {B : Fin (n + 1) → Subalgebra ℂ A}
    (hf : FreelyIndependent φ.toProbabilitySpace B) (p : Fin (n + 1) → A)
    (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, IsStarProjection (p i))
    (hE : ∀ i, φ.expectation (p i) = (1 / 2 : ℂ))
    (t : ℝ≥0) (ht : 0 < t) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hsuper : ((t : ℝ) / (2 : ℝ) ^ (n + 1)) * (1 + r) ^ (n + 1) ≤ r)
    (z : ℂ) (hz : ‖z‖ < t) :
    Summable (fun k : ℕ => ‖φ.expectation (iteratedPositiveProduct (n + 1) p ^ k) * z ^ k‖) := by
  obtain ⟨s, hzs, hst⟩ := exists_between (show ‖z‖₊ < t by exact_mod_cast hz)
  have hs : 0 < s := (show (0 : ℝ≥0) ≤ ‖z‖₊ from bot_le).trans_lt hzs
  have hb := φ.expectationInverseTaylorSeries_iteratedHalfProjection_radius_bound
    hφ n hf p hpB hp hE t ht r hr hr1 hsuper s hs hst
  have hzr : (‖z‖₊ : ℝ≥0∞) <
      (φ.expectationInverseTaylorSeries (iteratedPositiveProduct (n + 1) p)).radius :=
    (ENNReal.coe_lt_coe.mpr hzs).trans_le hb
  simpa only [expectationInverseTaylorSeries, FormalMultilinearSeries.ofScalars_norm,
    norm_mul, norm_pow, coe_nnnorm] using
    (φ.expectationInverseTaylorSeries (iteratedPositiveProduct (n + 1) p)).summable_norm_mul_pow hzr
/-- The genuinely summable coefficients are the real moments of the
ACTUAL probability law, throughout the majorant disk. -/
theorem summable_actual_iteratedHalfProjection_law_moments
    (hφ : IsTracial φ.toProbabilitySpace) (n : ℕ) {B : Fin (n + 1) → Subalgebra ℂ A}
    (hf : FreelyIndependent φ.toProbabilitySpace B) (p : Fin (n + 1) → A)
    (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, IsStarProjection (p i))
    (hE : ∀ i, φ.expectation (p i) = (1 / 2 : ℂ))
    (t : ℝ≥0) (ht : 0 < t) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hsuper : ((t : ℝ) / (2 : ℝ) ^ (n + 1)) * (1 + r) ^ (n + 1) ≤ r)
    (u : ℝ) (hu : 0 < u) (hut : u < t) :
    Summable (fun k : ℕ => u ^ k * ∫ x : ℝ, x ^ k
      ∂(iteratedPositiveProbabilityLaw φ (n + 1) p (fun i => (hp i).nonneg) : MeasureTheory.Measure ℝ)) := by
  let μ := iteratedPositiveProbabilityLaw φ (n + 1) p (fun i => (hp i).nonneg)
  have hpos : ∀ᵐ x ∂(μ : MeasureTheory.Measure ℝ), 0 ≤ x := by
    have hsupp : ∀ᵐ x ∂(μ : MeasureTheory.Measure ℝ), x ∈ (μ : MeasureTheory.Measure ℝ).support :=
      MeasureTheory.Measure.support_mem_ae
    exact hsupp.mono (fun _ hx => iteratedPositiveProbabilityLaw_support_nonneg φ _ p _ hx)
  have hs := φ.summable_actual_iteratedHalfProjection_moments hφ n hf p hpB hp hE t ht r hr hr1 hsuper
    (u : ℂ) (by simpa only [Complex.norm_real, Real.norm_of_nonneg hu.le] using hut)
  convert hs using 1
  funext k
  rw [iteratedPositiveProbabilityLaw_power_moment φ (n + 1) p (fun i => (hp i).nonneg) k]
  have hm0 : 0 ≤ ∫ x : ℝ, x ^ k ∂(μ : MeasureTheory.Measure ℝ) :=
    MeasureTheory.integral_nonneg_of_ae (hpos.mono (fun x hx => pow_nonneg hx k))
  change u ^ k * (∫ x : ℝ, x ^ k ∂(μ : MeasureTheory.Measure ℝ)) =
    ‖(((∫ x : ℝ, x ^ k ∂(μ : MeasureTheory.Measure ℝ)) : ℝ) : ℂ) * (u : ℂ) ^ k‖
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le,
    Real.norm_of_nonneg hm0]
  ring

/-- A proved scalar Picard supersolution below one gives an ACTUAL support
bound for the supplied finite free half-projection product law. No actual
support or moment-summability assumption is introduced. -/
theorem iteratedHalfProjection_law_support_of_picard_supersolution
    (hφ : IsTracial φ.toProbabilitySpace) (n : ℕ) {B : Fin (n + 1) → Subalgebra ℂ A}
    (hf : FreelyIndependent φ.toProbabilitySpace B) (p : Fin (n + 1) → A)
    (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, IsStarProjection (p i))
    (hE : ∀ i, φ.expectation (p i) = (1 / 2 : ℂ))
    (t : ℝ≥0) (ht : 0 < t) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hsuper : ((t : ℝ) / (2 : ℝ) ^ (n + 1)) * (1 + r) ^ (n + 1) ≤ r) :
    (iteratedPositiveProbabilityLaw φ (n + 1) p (fun i => (hp i).nonneg) : MeasureTheory.Measure ℝ).support ⊆
      Set.Iic (1 / (t : ℝ)) := by
  have hsupp : ∀ᵐ x ∂(iteratedPositiveProbabilityLaw φ (n + 1) p
      (fun i => (hp i).nonneg) : MeasureTheory.Measure ℝ),
      x ∈ (iteratedPositiveProbabilityLaw φ (n + 1) p
        (fun i => (hp i).nonneg) : MeasureTheory.Measure ℝ).support := MeasureTheory.Measure.support_mem_ae
  have hpos := hsupp.mono (fun _ hx => iteratedPositiveProbabilityLaw_support_nonneg φ _ p _ hx)
  have hint := spectralMeasure_integrable_pow φ
    (iteratedPositiveProduct_nonneg (n + 1) p (fun i => (hp i).nonneg)).isSelfAdjoint
  apply support_subset_Iic_of_subcritical_moment_summability _ hpos hint (1 / (t : ℝ))
    (one_div_pos.mpr (by exact_mod_cast ht))
  intro u hu hut
  exact φ.summable_actual_iteratedHalfProjection_law_moments hφ n hf p hpB hp hE t ht r hr hr1 hsuper
    u hu (by simpa using hut)
end StarProbabilitySpace
end FreeProbability

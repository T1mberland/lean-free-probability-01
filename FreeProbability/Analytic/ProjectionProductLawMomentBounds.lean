import FreeProbability.Analytic.ProjectionProductMomentContinuation

/-! # True positive-law moment coefficients and convergence from actual support -/

noncomputable section
open MeasureTheory
open scoped Topology NNReal ENNReal
namespace FreeProbability
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
namespace StarProbabilitySpace
variable (φ : FreeProbability.StarProbabilitySpace A)

/-- The true real coefficient sum of the spectral law. -/
def lawRealMomentSum (a : A) (ha : IsSelfAdjoint a) (u : ℝ) : ℝ :=
  ∑' k : ℕ, (∫ x : ℝ, x ^ k ∂spectralMeasure φ ha) * u ^ k

/-- True positive-law moments are nonnegative. -/
theorem spectralPowerMoment_nonneg (a : A) (ha : 0 ≤ a) (k : ℕ) :
    0 ≤ ∫ x : ℝ, x ^ k ∂spectralMeasure φ ha.isSelfAdjoint := by
  have hsupp : ∀ᵐ x ∂spectralMeasure φ ha.isSelfAdjoint,
      x ∈ (spectralMeasure φ ha.isSelfAdjoint).support := Measure.support_mem_ae
  apply integral_nonneg_of_ae
  filter_upwards [hsupp] with x hx
  exact pow_nonneg (spectrum_nonneg_of_nonneg ha (spectralMeasure_support_subset φ ha.isSelfAdjoint hx)) k

/-- At every real parameter the TRUE complex moment-series sum is the real
spectral moment sum embedded in the complex numbers. -/
theorem lawMomentSum_ofReal (a : A) (ha : IsSelfAdjoint a) (u : ℝ) :
    φ.lawMomentSum a (u : ℂ) = (φ.lawRealMomentSum a ha u : ℂ) := by
  change FormalMultilinearSeries.ofScalarsSum (fun k => φ.expectation (a ^ k)) (u : ℂ) = _
  rw [FormalMultilinearSeries.ofScalars_sum_eq, lawRealMomentSum, Complex.ofReal_tsum]
  apply tsum_congr
  intro k
  rw [spectralMeasure_power_moment φ ha k]
  simp only [smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_pow]

/-- Normalization and nonnegative true coefficients put the actual real
moment sum above one wherever its true series is summable. -/
theorem lawRealMomentSum_ge_one (a : A) (ha : 0 ≤ a) (u : ℝ) (hu : 0 ≤ u)
    (hs : Summable (fun k : ℕ => (∫ x : ℝ, x ^ k ∂spectralMeasure φ ha.isSelfAdjoint) * u ^ k)) :
    1 ≤ φ.lawRealMomentSum a ha.isSelfAdjoint u := by
  have h := hs.le_tsum 0
    (fun k _ => mul_nonneg (φ.spectralPowerMoment_nonneg a ha k) (pow_nonneg hu k))
  simpa [lawRealMomentSum] using h

/-- A bound on ACTUAL law support implies a radius bound for its true
moment Taylor series. Ambient norm and faithfulness are not involved. -/
theorem expectationInverseTaylorSeries_radius_of_spectral_support (a : A) (ha : 0 ≤ a)
    (b : ℝ) (hb : 0 ≤ b)
    (hbound : (spectralMeasure φ ha.isSelfAdjoint).support ⊆ Set.Iic b)
    (s : ℝ≥0) (hsb : (s : ℝ) * b < 1) :
    (s : ℝ≥0∞) ≤ (φ.expectationInverseTaylorSeries a).radius := by
  let μ := spectralProbabilityMeasure φ ha.isSelfAdjoint
  have hpos : ∀ᵐ x ∂(μ : Measure ℝ), 0 ≤ x := by
    have hsupp : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ (μ : Measure ℝ).support := Measure.support_mem_ae
    filter_upwards [hsupp] with x hx
    exact spectrum_nonneg_of_nonneg ha (spectralMeasure_support_subset φ ha.isSelfAdjoint hx)
  have hsum := summable_positive_moments_of_support_bound μ hpos
    (spectralMeasure_integrable_pow φ ha.isSelfAdjoint) b hb hbound s s.coe_nonneg hsb
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  convert hsum using 1
  funext k
  simp only [expectationInverseTaylorSeries, FormalMultilinearSeries.ofScalars_norm]
  rw [spectralMeasure_power_moment φ ha.isSelfAdjoint k]
  simp only [Complex.norm_real, Real.norm_of_nonneg (φ.spectralPowerMoment_nonneg a ha k)]
  dsimp [μ, spectralProbabilityMeasure]
  ring
end StarProbabilitySpace
end FreeProbability

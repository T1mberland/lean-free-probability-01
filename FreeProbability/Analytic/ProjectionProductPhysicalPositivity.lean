import FreeProbability.Analytic.ProjectionProductCauchyMoment

/-! # Actual positivity and integrability of the law exterior Cauchy branch -/

noncomputable section
open MeasureTheory
namespace FreeProbability

/-- Actual positive-law exterior Cauchy integrals have normalized value at
least one. This also verifies that the genuine integral is nonzero. -/
theorem realProbabilityCauchyTransform_normalized_ge_one (μ : ProbabilityMeasure ℝ)
    (hpos : ∀ᵐ y ∂(μ : Measure ℝ), 0 ≤ y)
    (hint : ∀ k : ℕ, Integrable (fun y : ℝ => y ^ k) (μ : Measure ℝ))
    (b : ℝ) (hb : 0 ≤ b) (hbound : (μ : Measure ℝ).support ⊆ Set.Iic b)
    (x : ℝ) (hxb : b < x) : 1 ≤ x * realProbabilityCauchyTransform μ x := by
  have hx : 0 < x := hb.trans_lt hxb
  have hux : (1 / x) * b < 1 := by
    simpa only [one_div, mul_comm, ← div_eq_mul_inv] using (div_lt_one hx).mpr hxb
  have hs := summable_positive_moments_of_support_bound μ hpos hint b hb hbound (1 / x)
    (one_div_pos.mpr hx).le hux
  have hnon (k : ℕ) : 0 ≤ (1 / x) ^ k * ∫ y : ℝ, y ^ k ∂(μ : Measure ℝ) :=
    mul_nonneg (pow_nonneg (one_div_pos.mpr hx).le k)
      (integral_nonneg_of_ae (hpos.mono (fun y hy => pow_nonneg hy k)))
  have h := hs.le_tsum 0 (fun k _ => hnon k)
  rw [realProbabilityCauchyTransform_eq_momentSum μ hpos hint b hb hbound x hxb]
  simpa [mul_comm] using h

/-- The actual exterior Cauchy kernel is integrable, not an undefined
Bochner integral assigned the value zero. -/
theorem integrable_realProbabilityCauchyTransform_kernel (μ : ProbabilityMeasure ℝ)
    (hpos : ∀ᵐ y ∂(μ : Measure ℝ), 0 ≤ y)
    (hint : ∀ k : ℕ, Integrable (fun y : ℝ => y ^ k) (μ : Measure ℝ))
    (b : ℝ) (hb : 0 ≤ b) (hbound : (μ : Measure ℝ).support ⊆ Set.Iic b)
    (x : ℝ) (hxb : b < x) : Integrable (fun y : ℝ => (x - y)⁻¹) (μ : Measure ℝ) := by
  have h := realProbabilityCauchyTransform_normalized_ge_one μ hpos hint b hb hbound x hxb
  by_contra hn
  rw [realProbabilityCauchyTransform, integral_undef hn, mul_zero] at h
  norm_num at h

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
namespace StarProbabilitySpace
variable (φ : FreeProbability.StarProbabilitySpace A)

/-- Positive first true moments make the actual real moment sum strictly
larger than one at positive parameters of genuine convergence. -/
theorem lawRealMomentSum_gt_one (a : A) (ha : 0 ≤ a) (u : ℝ) (hu : 0 < u)
    (hmean : 0 < ∫ y : ℝ, y ∂spectralMeasure φ ha.isSelfAdjoint)
    (hs : Summable (fun k : ℕ => (∫ y : ℝ, y ^ k ∂spectralMeasure φ ha.isSelfAdjoint) * u ^ k)) :
    1 < φ.lawRealMomentSum a ha.isSelfAdjoint u := by
  have h := lt_hasSum hs.hasSum 0
    (fun k _ => mul_nonneg (φ.spectralPowerMoment_nonneg a ha k) (pow_nonneg hu.le k))
    1 (by decide) (by simpa only [pow_one] using mul_pos hmean hu)
  simpa [lawRealMomentSum] using h

/-- The literal actual law Cauchy parameter in the positive exterior. -/
def halfProjectionExteriorW (L : ℕ) (p : Fin L → A) (hp : ∀ i, IsStarProjection (p i)) (x : ℝ) : ℝ :=
  x * realProbabilityCauchyTransform (iteratedPositiveProbabilityLaw φ L p (fun i => (hp i).nonneg)) x - 1

/-- The actual Cauchy parameter is positive on the FULL law right exterior,
with its first moment derived from the original half projections. -/
theorem halfProjectionExteriorW_pos
    (hφ : IsTracial φ.toProbabilitySpace) (L : ℕ) (hL : 2 ≤ L)
    {B : Fin L → Subalgebra ℂ A} (hf : FreelyIndependent φ.toProbabilitySpace B)
    (p : Fin L → A) (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, IsStarProjection (p i))
    (hE : ∀ i, φ.expectation (p i) = (1 / 2 : ℂ)) (x : ℝ) (hx : halfProjectionRightEdge L < x) :
    0 < φ.halfProjectionExteriorW L p hp x := by
  let a := iteratedPositiveProduct L p
  have ha : 0 ≤ a := iteratedPositiveProduct_nonneg L p (fun i => (hp i).nonneg)
  have hx0 : 0 < x := (halfProjectionRightEdge_pos L hL).trans hx
  have hmean : 0 < ∫ y : ℝ, y ∂spectralMeasure φ ha.isSelfAdjoint := by
    have hM := spectralMeasure_power_moment φ ha.isSelfAdjoint 1
    simp only [pow_one] at hM
    have hhalf := φ.expectation_iteratedHalfProjectionProduct hφ L hf p hpB hp hE
    have he : (∫ y : ℝ, y ∂spectralMeasure φ ha.isSelfAdjoint) = (1 / 2 : ℝ) ^ L := by
      apply Complex.ofReal_injective
      push_cast
      exact hM.symm.trans hhalf
    rw [he]
    positivity
  let μ := iteratedPositiveProbabilityLaw φ L p (fun i => (hp i).nonneg)
  have hpos : ∀ᵐ y ∂(μ : Measure ℝ), 0 ≤ y := by
    have hsupp : ∀ᵐ y ∂(μ : Measure ℝ), y ∈ (μ : Measure ℝ).support := Measure.support_mem_ae
    exact hsupp.mono (fun _ hy => iteratedPositiveProbabilityLaw_support_nonneg φ L p _ hy)
  have hub : (1 / x) * halfProjectionRightEdge L < 1 := by
    simpa only [one_div, mul_comm, ← div_eq_mul_inv] using (div_lt_one hx0).mpr hx
  have hs := summable_positive_moments_of_support_bound μ hpos (spectralMeasure_integrable_pow φ ha.isSelfAdjoint)
    (halfProjectionRightEdge L) (halfProjectionRightEdge_pos L hL).le
    (φ.iteratedHalfProjection_law_support_sharp_upper hφ L hL hf p hpB hp hE) (1 / x)
    (one_div_pos.mpr hx0).le hub
  have hsReal : Summable (fun k : ℕ => (∫ y : ℝ, y ^ k ∂spectralMeasure φ ha.isSelfAdjoint) * (1 / x) ^ k) := by
    convert hs using 1
    funext k
    dsimp [μ, iteratedPositiveProbabilityLaw, spectralProbabilityMeasure]
    ring
  have hI := φ.lawRealMomentSum_gt_one a ha (1 / x) (one_div_pos.mpr hx0) hmean hsReal
  unfold halfProjectionExteriorW
  rw [φ.iteratedHalfProjection_realCauchyTransform_eq_momentSum hφ L hL hf p hpB hp hE x hx]
  exact sub_pos.mpr hI
end StarProbabilitySpace
end FreeProbability

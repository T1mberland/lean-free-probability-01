import FreeProbability.Analytic.ProjectionProductSupportLower

/-! # Genuine exterior Cauchy integrals and actual positive-law moment sums -/

noncomputable section
open MeasureTheory
namespace FreeProbability

/-- The genuine real Cauchy integral of a supplied probability law. -/
def realProbabilityCauchyTransform (μ : ProbabilityMeasure ℝ) (x : ℝ) : ℝ :=
  ∫ y : ℝ, (x - y)⁻¹ ∂(μ : Measure ℝ)

/-- True positive moment series sum to the actual geometric-kernel integral
inside the reciprocal support bound, by absolute Bochner summation. -/
theorem positiveLaw_momentSum_eq_inverse_integral (μ : ProbabilityMeasure ℝ)
    (hpos : ∀ᵐ y ∂(μ : Measure ℝ), 0 ≤ y)
    (hint : ∀ k : ℕ, Integrable (fun y : ℝ => y ^ k) (μ : Measure ℝ))
    (b : ℝ) (hb : 0 ≤ b) (hbound : (μ : Measure ℝ).support ⊆ Set.Iic b)
    (u : ℝ) (hu : 0 ≤ u) (hub : u * b < 1) :
    (∑' k : ℕ, u ^ k * ∫ y : ℝ, y ^ k ∂(μ : Measure ℝ)) =
      ∫ y : ℝ, (1 - u * y)⁻¹ ∂(μ : Measure ℝ) := by
  have hsum := summable_positive_moments_of_support_bound μ hpos hint b hb hbound u hu hub
  have hF (k : ℕ) : Integrable (fun y : ℝ => u ^ k * y ^ k) (μ : Measure ℝ) :=
    (hint k).const_mul _
  have hnorm : Summable (fun k : ℕ => ∫ y : ℝ, ‖u ^ k * y ^ k‖ ∂(μ : Measure ℝ)) := by
    convert hsum using 1
    funext k
    rw [integral_congr_ae (hpos.mono (fun y hy =>
      Real.norm_of_nonneg (mul_nonneg (pow_nonneg hu k) (pow_nonneg hy k)))), integral_const_mul]
  have htsum := integral_tsum_of_summable_integral_norm hF hnorm
  have hsupp : ∀ᵐ y ∂(μ : Measure ℝ), y ∈ (μ : Measure ℝ).support := Measure.support_mem_ae
  have hkernel : (fun y : ℝ => ∑' k : ℕ, u ^ k * y ^ k) =ᵐ[(μ : Measure ℝ)] (fun y => (1 - u * y)⁻¹) := by
    filter_upwards [hpos, hsupp] with y hy hys
    have hnon : 0 ≤ u * y := mul_nonneg hu hy
    have hlt : u * y < 1 := (mul_le_mul_of_nonneg_left (hbound hys) hu).trans_lt hub
    simp only [← mul_pow]
    exact tsum_geometric_of_norm_lt_one (by rwa [Real.norm_of_nonneg hnon])
  simpa only [integral_const_mul] using htsum.trans (integral_congr_ae hkernel)

/-- The genuine real exterior Cauchy integral is exactly the TRUE law moment
series under reciprocal substitution. -/
theorem realProbabilityCauchyTransform_eq_momentSum (μ : ProbabilityMeasure ℝ)
    (hpos : ∀ᵐ y ∂(μ : Measure ℝ), 0 ≤ y)
    (hint : ∀ k : ℕ, Integrable (fun y : ℝ => y ^ k) (μ : Measure ℝ))
    (b : ℝ) (hb : 0 ≤ b) (hbound : (μ : Measure ℝ).support ⊆ Set.Iic b)
    (x : ℝ) (hxb : b < x) :
    x * realProbabilityCauchyTransform μ x =
      ∑' k : ℕ, (∫ y : ℝ, y ^ k ∂(μ : Measure ℝ)) * (1 / x) ^ k := by
  have hx : 0 < x := hb.trans_lt hxb
  have hux : (1 / x) * b < 1 := by
    simpa only [one_div, mul_comm, ← div_eq_mul_inv] using (div_lt_one hx).mpr hxb
  have he := positiveLaw_momentSum_eq_inverse_integral μ hpos hint b hb hbound (1 / x)
    (one_div_pos.mpr hx).le hux
  have hkernel (y : ℝ) : (1 - (1 / x) * y)⁻¹ = x * (x - y)⁻¹ := by
    have hnorm : 1 - (1 / x) * y = (x - y) / x := by field_simp
    rw [hnorm, inv_div, div_eq_mul_inv]
  rw [realProbabilityCauchyTransform, ← integral_const_mul]
  calc
    _ = ∫ y : ℝ, (1 - (1 / x) * y)⁻¹ ∂(μ : Measure ℝ) := integral_congr_ae (ae_of_all _ (fun y => (hkernel y).symm))
    _ = ∑' k : ℕ, (∫ y : ℝ, y ^ k ∂(μ : Measure ℝ)) * (1 / x) ^ k := by
      simpa only [mul_comm] using he.symm
namespace StarProbabilitySpace
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (φ : FreeProbability.StarProbabilitySpace A)

/-- On the FULL actual law right exterior, its literal Cauchy integral
matches the true law moment sum. No ambient resolvent-set assumption is used. -/
theorem iteratedHalfProjection_realCauchyTransform_eq_momentSum
    (hφ : IsTracial φ.toProbabilitySpace) (L : ℕ) (hL : 2 ≤ L)
    {B : Fin L → Subalgebra ℂ A} (hf : FreelyIndependent φ.toProbabilitySpace B)
    (p : Fin L → A) (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, IsStarProjection (p i))
    (hE : ∀ i, φ.expectation (p i) = (1 / 2 : ℂ)) (x : ℝ) (hx : halfProjectionRightEdge L < x) :
    x * realProbabilityCauchyTransform
      (iteratedPositiveProbabilityLaw φ L p (fun i => (hp i).nonneg)) x =
      φ.lawRealMomentSum (iteratedPositiveProduct L p)
        (iteratedPositiveProduct_nonneg L p (fun i => (hp i).nonneg)).isSelfAdjoint (1 / x) := by
  let μ := iteratedPositiveProbabilityLaw φ L p (fun i => (hp i).nonneg)
  have hpos : ∀ᵐ y ∂(μ : Measure ℝ), 0 ≤ y := by
    have hsupp : ∀ᵐ y ∂(μ : Measure ℝ), y ∈ (μ : Measure ℝ).support := Measure.support_mem_ae
    exact hsupp.mono (fun _ hy => iteratedPositiveProbabilityLaw_support_nonneg φ L p _ hy)
  exact realProbabilityCauchyTransform_eq_momentSum μ hpos
    (spectralMeasure_integrable_pow φ (iteratedPositiveProduct_nonneg L p (fun i => (hp i).nonneg)).isSelfAdjoint)
    (halfProjectionRightEdge L) (halfProjectionRightEdge_pos L hL).le
    (φ.iteratedHalfProjection_law_support_sharp_upper hφ L hL hf p hpB hp hE) x hx
end StarProbabilitySpace
end FreeProbability

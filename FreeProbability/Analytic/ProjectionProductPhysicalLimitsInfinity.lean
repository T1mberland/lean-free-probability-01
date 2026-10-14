import FreeProbability.Analytic.ProjectionProductPhysicalLimitsCriticalEdge

/-! # Genuine infinity normalization of the physical law Cauchy branch -/

noncomputable section
open scoped Topology
open Filter
namespace FreeProbability
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
namespace StarProbabilitySpace
variable (φ : FreeProbability.StarProbabilitySpace A)

/-- The ACTUAL exterior parameter tends to zero at positive infinity.
This is derived from the true law moment germ, without faithfulness. -/
theorem tendsto_halfProjectionExteriorW_atTop_zero
    (hφ : IsTracial φ.toProbabilitySpace) (L : ℕ) (hL : 2 ≤ L)
    {B : Fin L → Subalgebra ℂ A} (hf : FreelyIndependent φ.toProbabilitySpace B)
    (p : Fin L → A) (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, IsStarProjection (p i))
    (hE : ∀ i, φ.expectation (p i) = (1 / 2 : ℂ)) :
    Tendsto (φ.halfProjectionExteriorW L p hp) atTop (𝓝 0) := by
  let a := iteratedPositiveProduct L p
  have ha : 0 ≤ a := iteratedPositiveProduct_nonneg L p (fun i => (hp i).nonneg)
  have hu : Tendsto (fun x : ℝ => ((1 / x : ℝ) : ℂ)) atTop (𝓝 0) := by
    simpa only [one_div, Complex.ofReal_zero, Function.comp_def] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp (tendsto_inv_atTop_zero :
        Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0))
  have hm := (φ.analyticAt_momentGeneratingFunction_zero a).continuousAt.tendsto.comp hu
  have hm0 : Tendsto (fun x : ℝ => (φ.momentGeneratingFunction a ((1 / x : ℝ) : ℂ)).re)
      atTop (𝓝 0) := by
    simpa [Function.comp_def] using Complex.continuous_re.continuousAt.tendsto.comp hm
  apply hm0.congr'
  have hlarge : ∀ᶠ x : ℝ in atTop, halfProjectionRightEdge L < x := eventually_gt_atTop _
  have hlocal := hu.eventually (φ.lawMomentSum_eq_expectation_inverse_eventually a)
  filter_upwards [hlarge, hlocal] with x hx he
  have hI : φ.lawMomentSum a ((1 / x : ℝ) : ℂ) =
      φ.momentGeneratingFunction a ((1 / x : ℝ) : ℂ) + 1 := by
    rw [he]
    simp [momentGeneratingFunction]
  rw [φ.lawMomentSum_ofReal a ha.isSelfAdjoint (1 / x)] at hI
  have hr := congrArg Complex.re hI
  simp only [Complex.ofReal_re, Complex.add_re, Complex.one_re] at hr
  unfold halfProjectionExteriorW
  rw [φ.iteratedHalfProjection_realCauchyTransform_eq_momentSum hφ L hL hf p hpB hp hE x hx]
  change (φ.momentGeneratingFunction a ((1 / x : ℝ) : ℂ)).re =
    φ.lawRealMomentSum a ha.isSelfAdjoint (1 / x) - 1
  linarith

/-- The genuine law Cauchy transform has its probability normalization at
positive infinity: x G_mu(x) tends to one. -/
theorem tendsto_halfProjection_normalized_realCauchyTransform_atTop_one
    (hφ : IsTracial φ.toProbabilitySpace) (L : ℕ) (hL : 2 ≤ L)
    {B : Fin L → Subalgebra ℂ A} (hf : FreelyIndependent φ.toProbabilitySpace B)
    (p : Fin L → A) (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, IsStarProjection (p i))
    (hE : ∀ i, φ.expectation (p i) = (1 / 2 : ℂ)) :
    Tendsto (fun x : ℝ => x * realProbabilityCauchyTransform
      (iteratedPositiveProbabilityLaw φ L p (fun i => (hp i).nonneg)) x) atTop (𝓝 1) := by
  have h := (φ.tendsto_halfProjectionExteriorW_atTop_zero hφ L hL hf p hpB hp hE).add_const 1
  simpa only [halfProjectionExteriorW, sub_add_cancel, zero_add] using h
end StarProbabilitySpace
end FreeProbability

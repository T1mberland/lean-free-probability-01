import FreeProbability.Analytic.ProjectionProductPhysicalLimitsInfinity

/-! # The infinite-coordinate physical boundary at length two -/

noncomputable section
open scoped Topology
open Filter
namespace FreeProbability

/-- The length-two exterior curve has a strictly positive correction to one. -/
theorem halfProjectionExteriorCurve_two (w : ℝ) (hw : 0 < w) :
    halfProjectionExteriorCurve 2 w = 1 + 1 / (4 * w * (1 + w)) := by
  unfold halfProjectionExteriorCurve
  norm_num
  have h1 : 1 + w ≠ 0 := by linarith
  have hw0 : w ≠ 0 := ne_of_gt hw
  field_simp
  ring

/-- The length-two physical curve is strictly decreasing on its whole positive domain. -/
theorem halfProjectionExteriorCurve_two_strictAntiOn :
    StrictAntiOn (halfProjectionExteriorCurve 2) (Set.Ioi 0) := by
  intro v hv w hw hvw
  change 0 < v at hv
  change 0 < w at hw
  rw [halfProjectionExteriorCurve_two v hv, halfProjectionExteriorCurve_two w hw]
  have hdv : 0 < 4 * v * (1 + v) := by positivity
  have hdw : 4 * v * (1 + v) < 4 * w * (1 + w) := by nlinarith
  exact add_lt_add_right (one_div_lt_one_div_of_lt hdv hdw) 1

/-- The length-two edge corresponds to w tending to infinity, not a finite
critical exterior coordinate. -/
theorem tendsto_halfProjectionExteriorCurve_two_atTop_one :
    Tendsto (halfProjectionExteriorCurve 2) atTop (𝓝 1) := by
  have hi : Tendsto (fun w : ℝ => w⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hplus : Tendsto (fun w : ℝ => 1 + w) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (b - 1)] with w hw
    linarith
  have hi1 : Tendsto (fun w : ℝ => (1 + w)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hplus
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).add ((hi.mul hi1).const_mul (1 / 4 : ℝ))
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with w hw
  rw [halfProjectionExteriorCurve_two w hw]
  simp only [one_div, mul_inv_rev]
  ring

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
namespace StarProbabilitySpace
variable (φ : FreeProbability.StarProbabilitySpace A)

/-- The actual length-two product law has greatest support point one. -/
theorem iteratedTwoHalfProjection_law_support_isGreatest_one
    (hφ : IsTracial φ.toProbabilitySpace) {B : Fin 2 → Subalgebra ℂ A}
    (hf : FreelyIndependent φ.toProbabilitySpace B) (p : Fin 2 → A)
    (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, IsStarProjection (p i))
    (hE : ∀ i, φ.expectation (p i) = (1 / 2 : ℂ)) :
    IsGreatest ((iteratedPositiveProbabilityLaw φ 2 p (fun i => (hp i).nonneg) :
      MeasureTheory.Measure ℝ).support) 1 := by
  have hedge : halfProjectionRightEdge 2 = 1 := by norm_num [halfProjectionRightEdge]
  simpa only [hedge] using
    φ.iteratedHalfProjection_law_support_isGreatest hφ 2 (by omega) hf p hpB hp hE

/-- As the ACTUAL exterior point approaches the ACTUAL length-two law edge
from the right, its genuine Cauchy parameter tends to positive infinity. -/
theorem tendsto_halfProjectionExteriorW_two_right_edge_atTop
    (hφ : IsTracial φ.toProbabilitySpace) {B : Fin 2 → Subalgebra ℂ A}
    (hf : FreelyIndependent φ.toProbabilitySpace B) (p : Fin 2 → A)
    (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, IsStarProjection (p i))
    (hE : ∀ i, φ.expectation (p i) = (1 / 2 : ℂ)) :
    Tendsto (φ.halfProjectionExteriorW 2 p hp) (𝓝[Set.Ioi 1] 1) atTop := by
  apply tendsto_atTop.2
  intro b
  let M : ℝ := max b 1
  have hM : 0 < M := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  have hedge : halfProjectionRightEdge 2 = 1 := by norm_num [halfProjectionRightEdge]
  have hc : 1 < halfProjectionExteriorCurve 2 M := by
    rw [halfProjectionExteriorCurve_two M hM]
    have hd : 0 < 1 / (4 * M * (1 + M)) := by positivity
    linarith
  have hnear : ∀ᶠ x : ℝ in 𝓝[Set.Ioi 1] 1, x < halfProjectionExteriorCurve 2 M :=
    (eventually_lt_nhds hc).filter_mono nhdsWithin_le_nhds
  filter_upwards [hnear, self_mem_nhdsWithin] with x hx hxr
  have hxedge : halfProjectionRightEdge 2 < x := by simpa only [hedge, Set.mem_Ioi] using hxr
  have hw := φ.halfProjectionExteriorW_pos hφ 2 (by omega) hf p hpB hp hE x hxedge
  have he := φ.halfProjectionExteriorW_curve_equation hφ 2 (by omega) hf p hpB hp hE x hxedge
  have hMw : M < φ.halfProjectionExteriorW 2 p hp x := by
    by_contra hn
    have hle := halfProjectionExteriorCurve_two_strictAntiOn.antitoneOn hw hM (le_of_not_gt hn)
    rw [he] at hle
    linarith
  exact (le_max_left b 1).trans hMw.le
end StarProbabilitySpace
end FreeProbability

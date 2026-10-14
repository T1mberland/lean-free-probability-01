import FreeProbability.Analytic.ProjectionProductCurveMaximum

/-! # Genuine analytic continuation of the actual law moment equation -/

noncomputable section
open scoped Topology NNReal ENNReal
namespace FreeProbability
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
namespace StarProbabilitySpace
variable (φ : FreeProbability.StarProbabilitySpace A)

/-- The sum of the TRUE moment coefficients, as distinct from a possibly
undefined ambient resolvent outside its original domain. -/
def lawMomentSum (a : A) : ℂ → ℂ := (φ.expectationInverseTaylorSeries a).sum

/-- Near zero the true moment sum is the actual inverse expectation. -/
theorem lawMomentSum_eq_expectation_inverse_eventually (a : A) :
    φ.lawMomentSum a =ᶠ[𝓝 0] (fun z : ℂ => φ.expectation (Ring.inverse (1 - z • a))) := by
  have hsmall : ∀ᶠ z : ℂ in 𝓝 0, ‖z‖ * ‖a‖ < 1 :=
    (continuous_norm.mul_const ‖a‖).continuousAt.eventually_lt continuousAt_const (by simp)
  filter_upwards [hsmall] with z hz
  change FormalMultilinearSeries.ofScalarsSum (fun k => φ.expectation (a ^ k)) z = _
  rw [FormalMultilinearSeries.ofScalars_sum_eq]
  simpa only [smul_eq_mul, mul_comm] using (φ.hasSum_expectation_inverse a z hz).tsum_eq

/-- The TRUE law moment sum satisfies the cleared half-projection polynomial
near zero, with all inputs derived from the original free family. -/
theorem lawMomentSum_iteratedHalfProjection_equation_eventually
    (hφ : IsTracial φ.toProbabilitySpace) (n : ℕ) {B : Fin (n + 1) → Subalgebra ℂ A}
    (hf : FreelyIndependent φ.toProbabilitySpace B) (p : Fin (n + 1) → A)
    (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, IsStarProjection (p i))
    (hE : ∀ i, φ.expectation (p i) = (1 / 2 : ℂ)) :
    ∀ᶠ z : ℂ in 𝓝 0,
      let I := φ.lawMomentSum (iteratedPositiveProduct (n + 1) p) z
      z * (I - (1 / 2 : ℂ)) ^ (n + 1) = (I - 1) * I ^ n := by
  filter_upwards [φ.lawMomentSum_eq_expectation_inverse_eventually (iteratedPositiveProduct (n + 1) p),
    φ.momentGeneratingFunction_iteratedHalfProjectionProduct_equation_eventually hφ n hf p hpB hp hE]
    with z hI hz
  have he : φ.lawMomentSum (iteratedPositiveProduct (n + 1) p) z =
      φ.momentGeneratingFunction (iteratedPositiveProduct (n + 1) p) z + 1 := by
    rw [hI]
    simp [momentGeneratingFunction]
  simp only [he, add_sub_cancel_right]
  have hhalf : φ.momentGeneratingFunction (iteratedPositiveProduct (n + 1) p) z + 1 - (1 / 2 : ℂ) =
      φ.momentGeneratingFunction (iteratedPositiveProduct (n + 1) p) z + (1 / 2 : ℂ) := by ring
  rw [hhalf]
  simpa only [add_comm] using hz

/-- The actual law moment polynomial continues throughout any disk inside
the TRUE moment-series radius, even beyond the ambient norm resolvent disk.
No faithfulness or global ambient inverse is required. -/
theorem lawMomentSum_iteratedHalfProjection_equation_on_disk
    (hφ : IsTracial φ.toProbabilitySpace) (n : ℕ) {B : Fin (n + 1) → Subalgebra ℂ A}
    (hf : FreelyIndependent φ.toProbabilitySpace B) (p : Fin (n + 1) → A)
    (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, IsStarProjection (p i))
    (hE : ∀ i, φ.expectation (p i) = (1 / 2 : ℂ))
    (s : ℝ≥0) (hs : 0 < s)
    (hbound : (s : ℝ≥0∞) ≤ (φ.expectationInverseTaylorSeries (iteratedPositiveProduct (n + 1) p)).radius)
    (z : ℂ) (hz : ‖z‖ < s) :
    let I := φ.lawMomentSum (iteratedPositiveProduct (n + 1) p) z
    z * (I - (1 / 2 : ℂ)) ^ (n + 1) = (I - 1) * I ^ n := by
  let a := iteratedPositiveProduct (n + 1) p
  let F := fun z : ℂ => z * (φ.lawMomentSum a z - (1 / 2 : ℂ)) ^ (n + 1) -
    (φ.lawMomentSum a z - 1) * φ.lawMomentSum a z ^ n
  have hI : AnalyticOnNhd ℂ (φ.lawMomentSum a) (Metric.ball 0 s) := by
    intro y hy
    apply (φ.expectationInverseTaylorSeries a).analyticOnNhd
    have hys : ‖y‖₊ < s := by
      exact_mod_cast (show ‖y‖ < s by simpa only [Metric.mem_ball, dist_zero_right] using hy)
    simp only [Metric.mem_eball, edist_zero_right]
    exact (ENNReal.coe_lt_coe.mpr hys).trans_le hbound
  have hF : AnalyticOnNhd ℂ F (Metric.ball 0 s) := by
    intro y hy
    exact (analyticAt_id.mul (((hI y hy).sub analyticAt_const).pow (n + 1))).sub
      (((hI y hy).sub analyticAt_const).mul ((hI y hy).pow n))
  have hevent : F =ᶠ[𝓝 0] 0 := by
    filter_upwards [φ.lawMomentSum_iteratedHalfProjection_equation_eventually hφ n hf p hpB hp hE]
      with y hy
    exact sub_eq_zero.mpr hy
  have hzero := hF.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball (0 : ℂ) (s : ℝ)).isPreconnected (by simp; exact_mod_cast hs) hevent
  exact sub_eq_zero.mp (hzero (by simpa only [Metric.mem_ball, dist_zero_right] using hz))
end StarProbabilitySpace
end FreeProbability

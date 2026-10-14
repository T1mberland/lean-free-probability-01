import FreeProbability.Analytic.CauchyHalfPlane
import Mathlib.Analysis.Complex.Convex

/-! # Analytic continuation of Cauchy-transform equality

Equality of power moments determines Cauchy transforms on connected common
resolvent domains meeting the exterior region. For selfadjoint variables this
includes every nonreal argument, across different ambient algebras.
-/

namespace FreeProbability.StarProbabilitySpace
open scoped Topology
variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (φ : FreeProbability.StarProbabilitySpace A) (ψ : FreeProbability.StarProbabilitySpace B)

theorem cauchyTransform_eqOn_of_powerMoments (a : A) (b : B)
    (hm : ∀ k : ℕ, φ.expectation (a ^ k) = ψ.expectation (b ^ k))
    (U : Set ℂ) (hU : IsPreconnected U)
    (hA : U ⊆ resolventSet ℂ a) (hB : U ⊆ resolventSet ℂ b)
    (z₀ : ℂ) (hz₀ : z₀ ∈ U) (ha : ‖a‖ < ‖z₀‖) (hb : ‖b‖ < ‖z₀‖) :
    Set.EqOn (φ.cauchyTransform a) (ψ.cauchyTransform b) U := by
  have hEA : ∀ᶠ z in 𝓝 z₀, ‖a‖ < ‖z‖ :=
    continuousAt_const.eventually_lt continuous_norm.continuousAt ha
  have hEB : ∀ᶠ z in 𝓝 z₀, ‖b‖ < ‖z‖ :=
    continuousAt_const.eventually_lt continuous_norm.continuousAt hb
  have he : φ.cauchyTransform a =ᶠ[𝓝 z₀] ψ.cauchyTransform b := by
    filter_upwards [hEA, hEB] with z ha hb
    exact φ.cauchyTransform_eq_of_powerMoments ψ a b hm z ha hb
  exact ((φ.analyticOnNhd_cauchyTransform a).mono hA).eqOn_of_preconnected_of_eventuallyEq
    ((ψ.analyticOnNhd_cauchyTransform b).mono hB) hU hz₀ he

theorem cauchyTransform_eq_of_powerMoments_upperHalfPlane (a : A) (b : B)
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (hm : ∀ k : ℕ, φ.expectation (a ^ k) = ψ.expectation (b ^ k))
    (z : ℂ) (hz : 0 < z.im) : φ.cauchyTransform a z = ψ.cauchyTransform b z := by
  let R : ℝ := ‖a‖ + ‖b‖ + 1
  let z₀ : ℂ := (R : ℂ) * Complex.I
  have hR : 0 < R := by dsimp [R]; positivity
  have hi : z₀.im = R := by simp [z₀]
  have hn : R ≤ ‖z₀‖ := hi ▸ Complex.im_le_norm z₀
  have hNA : ‖a‖ < ‖z₀‖ := lt_of_lt_of_le (by dsimp [R]; linarith [norm_nonneg b]) hn
  have hNB : ‖b‖ < ‖z₀‖ := lt_of_lt_of_le (by dsimp [R]; linarith [norm_nonneg a]) hn
  apply φ.cauchyTransform_eqOn_of_powerMoments ψ a b hm {w : ℂ | 0 < w.im}
    (convex_halfSpace_im_gt 0).isPreconnected
    (fun w hw => selfAdjoint_mem_resolventSet_of_im_ne_zero a ha w hw.ne')
    (fun w hw => selfAdjoint_mem_resolventSet_of_im_ne_zero b hb w hw.ne')
    z₀ (by simpa only [Set.mem_ofPred_eq, hi] using hR) hNA hNB
  exact hz


theorem cauchyTransform_eq_of_powerMoments_lowerHalfPlane (a : A) (b : B)
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (hm : ∀ k : ℕ, φ.expectation (a ^ k) = ψ.expectation (b ^ k))
    (z : ℂ) (hz : z.im < 0) : φ.cauchyTransform a z = ψ.cauchyTransform b z := by
  let R : ℝ := ‖a‖ + ‖b‖ + 1
  let z₀ : ℂ := -(R : ℂ) * Complex.I
  have hR : 0 < R := by dsimp [R]; positivity
  have hi : z₀.im = -R := by simp [z₀]
  have hn : R ≤ ‖z₀‖ := by
    simpa only [hi, abs_neg, abs_of_pos hR] using Complex.abs_im_le_norm z₀
  have hNA : ‖a‖ < ‖z₀‖ := lt_of_lt_of_le (by dsimp [R]; linarith [norm_nonneg b]) hn
  have hNB : ‖b‖ < ‖z₀‖ := lt_of_lt_of_le (by dsimp [R]; linarith [norm_nonneg a]) hn
  apply φ.cauchyTransform_eqOn_of_powerMoments ψ a b hm {w : ℂ | w.im < 0}
    (convex_halfSpace_im_lt 0).isPreconnected
    (fun w hw => selfAdjoint_mem_resolventSet_of_im_ne_zero a ha w hw.ne)
    (fun w hw => selfAdjoint_mem_resolventSet_of_im_ne_zero b hb w hw.ne)
    z₀ (by simpa only [Set.mem_ofPred_eq, hi] using neg_neg_of_pos hR) hNA hNB
  exact hz

/-- For selfadjoint variables, common power moments determine the resolvent
expectations at every nonreal argument, without a common norm-ball restriction. -/
theorem cauchyTransform_eq_of_powerMoments_nonreal (a : A) (b : B)
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (hm : ∀ k : ℕ, φ.expectation (a ^ k) = ψ.expectation (b ^ k))
    (z : ℂ) (hz : z.im ≠ 0) : φ.cauchyTransform a z = ψ.cauchyTransform b z := by
  rcases lt_or_gt_of_ne hz with hn | hp
  · exact φ.cauchyTransform_eq_of_powerMoments_lowerHalfPlane ψ a b ha hb hm z hn
  · exact φ.cauchyTransform_eq_of_powerMoments_upperHalfPlane ψ a b ha hb hm z hp

end FreeProbability.StarProbabilitySpace

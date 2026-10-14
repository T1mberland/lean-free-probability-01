import FreeProbability.Analytic.Transform

/-! # Local inverse uniqueness and naturality of analytic transforms

S-transforms are invariant under equality of power moments and scale inversely
under multiplication of the variable by a nonzero scalar. The statements are
equalities of analytic germs, with their first-moment domain explicit.
-/

namespace FreeProbability.StarProbabilitySpace
open scoped Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (φ : FreeProbability.StarProbabilitySpace A)

theorem momentInverse_eq_of_eventually_right_inverse (a : A) (h : φ.expectation a ≠ 0)
    (g : ℂ → ℂ) (hg : ContinuousAt g 0) (hg0 : g 0 = 0)
    (hfg : ∀ᶠ w in 𝓝 (0 : ℂ), φ.momentGeneratingFunction a (g w) = w) :
    φ.momentInverse a h =ᶠ[𝓝 (0 : ℂ)] g := by
  have ht : Filter.Tendsto g (𝓝 0) (𝓝 0) := by simpa only [hg0] using hg.tendsto
  have he := ht.eventually (φ.momentInverse_eventually_left_inverse a h)
  filter_upwards [he, hfg] with w hw hfw
  rw [hfw] at hw
  exact hw

omit [PartialOrder A] [StarOrderedRing A] in
theorem momentGeneratingFunction_smul (a : A) (c w : ℂ) :
    φ.momentGeneratingFunction (c • a) w = φ.momentGeneratingFunction a (c * w) := by
  simp only [momentGeneratingFunction, smul_smul, mul_comm c w]

omit [PartialOrder A] [StarOrderedRing A] in
theorem expectation_smul_ne_zero (a : A) (h : φ.expectation a ≠ 0)
    (c : ℂ) (hc : c ≠ 0) : φ.expectation (c • a) ≠ 0 := by
  rw [map_smul, smul_eq_mul]
  exact mul_ne_zero hc h

theorem momentInverse_smul_eventually (a : A) (h : φ.expectation a ≠ 0)
    (c : ℂ) (hc : c ≠ 0) :
    φ.momentInverse (c • a) (φ.expectation_smul_ne_zero a h c hc) =ᶠ[𝓝 (0 : ℂ)]
      fun w => c⁻¹ * φ.momentInverse a h w := by
  apply φ.momentInverse_eq_of_eventually_right_inverse
  · exact continuousAt_const.mul (φ.analyticAt_momentInverse_zero a h).continuousAt
  · simp
  · filter_upwards [φ.momentInverse_eventually_right_inverse a h] with w hw
    rw [φ.momentGeneratingFunction_smul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
    exact hw

theorem sTransform_smul_eventually (a : A) (h : φ.expectation a ≠ 0)
    (c : ℂ) (hc : c ≠ 0) :
    φ.sTransform (c • a) (φ.expectation_smul_ne_zero a h c hc) =ᶠ[𝓝 (0 : ℂ)]
      fun w => c⁻¹ * φ.sTransform a h w := by
  filter_upwards [φ.momentInverse_smul_eventually a h c hc] with w hw
  by_cases hz : w = 0
  · simp [hz, map_smul, smul_eq_mul, mul_inv_rev, mul_comm]
  · rw [φ.sTransform_eq _ _ w hz, φ.sTransform_eq _ _ w hz, hw]
    ring


theorem momentGeneratingFunction_eventually_eq_of_powerMoments
    {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (ψ : FreeProbability.StarProbabilitySpace B) (a : A) (b : B)
    (hm : ∀ k : ℕ, φ.expectation (a ^ k) = ψ.expectation (b ^ k)) :
    φ.momentGeneratingFunction a =ᶠ[𝓝 (0 : ℂ)] ψ.momentGeneratingFunction b := by
  have ha : ∀ᶠ w in 𝓝 (0 : ℂ), ‖w‖ * ‖a‖ < 1 :=
    (continuous_norm.mul_const ‖a‖).continuousAt.eventually_lt continuousAt_const (by simp)
  have hb : ∀ᶠ w in 𝓝 (0 : ℂ), ‖w‖ * ‖b‖ < 1 :=
    (continuous_norm.mul_const ‖b‖).continuousAt.eventually_lt continuousAt_const (by simp)
  filter_upwards [ha, hb] with w ha hb
  exact φ.momentGeneratingFunction_eq_of_powerMoments ψ a b hm w ha hb

theorem momentInverse_eventually_eq_of_powerMoments
    {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (ψ : FreeProbability.StarProbabilitySpace B) (a : A) (b : B)
    (hm : ∀ k : ℕ, φ.expectation (a ^ k) = ψ.expectation (b ^ k))
    (ha : φ.expectation a ≠ 0) (hb : ψ.expectation b ≠ 0) :
    φ.momentInverse a ha =ᶠ[𝓝 (0 : ℂ)] ψ.momentInverse b hb := by
  apply φ.momentInverse_eq_of_eventually_right_inverse
  · exact (ψ.analyticAt_momentInverse_zero b hb).continuousAt
  · exact ψ.momentInverse_zero b hb
  · have ht : Filter.Tendsto (ψ.momentInverse b hb) (𝓝 0) (𝓝 0) := by
      simpa only [momentInverse_zero] using (ψ.analyticAt_momentInverse_zero b hb).continuousAt.tendsto
    have he := ht.eventually (φ.momentGeneratingFunction_eventually_eq_of_powerMoments ψ a b hm)
    filter_upwards [he, ψ.momentInverse_eventually_right_inverse b hb] with w he hw
    rw [he]
    exact hw

theorem sTransform_eventually_eq_of_powerMoments
    {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (ψ : FreeProbability.StarProbabilitySpace B) (a : A) (b : B)
    (hm : ∀ k : ℕ, φ.expectation (a ^ k) = ψ.expectation (b ^ k))
    (ha : φ.expectation a ≠ 0) (hb : ψ.expectation b ≠ 0) :
    φ.sTransform a ha =ᶠ[𝓝 (0 : ℂ)] ψ.sTransform b hb := by
  have hfirst : φ.expectation a = ψ.expectation b := by simpa only [pow_one] using hm 1
  filter_upwards [φ.momentInverse_eventually_eq_of_powerMoments ψ a b hm ha hb] with w hw
  by_cases hz : w = 0
  · simp only [hz, sTransform_zero, hfirst]
  · rw [φ.sTransform_eq _ _ w hz, ψ.sTransform_eq _ _ w hz, hw]

end FreeProbability.StarProbabilitySpace

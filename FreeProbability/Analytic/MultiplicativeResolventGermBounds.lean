import FreeProbability.Analytic.Transform
import FreeProbability.Algebraic.FreenessClosureResolventBounds
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Asymptotics.Ring

/-! # Actual inverse-germ centered correction tends to zero -/

noncomputable section
open scoped Topology
open Filter
namespace FreeProbability.StarProbabilitySpace
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (φ : FreeProbability.StarProbabilitySpace A)

/-- Actual centered resolvents along the genuine local moment inverse are O(w). -/
theorem centered_momentInverse_resolvent_isBigO (a : A) (ha : φ.expectation a ≠ 0) :
    (fun w : ℂ => φ.toProbabilitySpace.center
      (Ring.inverse (1 - φ.momentInverse a ha w • a))) =O[𝓝 0] (fun w : ℂ => w) := by
  have ht : Filter.Tendsto (φ.momentInverse a ha) (𝓝 0) (𝓝 0) := by
    simpa only [φ.momentInverse_zero] using (φ.analyticAt_momentInverse_zero a ha).continuousAt.tendsto
  have hχ : φ.momentInverse a ha =O[𝓝 0] (fun w : ℂ => w) := by
    simpa only [φ.momentInverse_zero, sub_zero] using
      (φ.hasStrictDerivAt_momentInverse_zero a ha).hasDerivAt.isBigO_sub
  have h := (φ.toProbabilitySpace.center_inverse_one_sub_smul_isBigO φ.continuous_expectation a).comp_tendsto ht
  simpa only [Function.comp_def] using h.trans hχ

/-- The actual centered Neumann correction is O(w), including its defined
value zero at the removable point. -/
theorem multiplicative_centered_correction_isBigO (a b : A)
    (ha : φ.expectation a ≠ 0) (hb : φ.expectation b ≠ 0) :
    (fun w : ℂ => (w * (1 + w))⁻¹ •
      (φ.toProbabilitySpace.center (Ring.inverse (1 - φ.momentInverse a ha w • a)) *
        φ.toProbabilitySpace.center (Ring.inverse (1 - φ.momentInverse b hb w • b))))
      =O[𝓝 0] (fun w : ℂ => w) := by
  have hconst : (fun w : ℂ => (1 + w)⁻¹) =O[𝓝 0] (fun _ : ℂ => (1 : ℂ)) :=
    ((continuousAt_const.add continuousAt_id).inv₀ (by simp)).isBigO
  have hcoeff : (fun w : ℂ => (w * (1 + w))⁻¹) =O[𝓝 0] (fun w : ℂ => w⁻¹) := by
    simpa only [mul_inv_rev, one_mul] using hconst.mul (Asymptotics.isBigO_refl (fun w : ℂ => w⁻¹) (𝓝 0))
  have h := hcoeff.smul ((φ.centered_momentInverse_resolvent_isBigO a ha).mul
    (φ.centered_momentInverse_resolvent_isBigO b hb))
  apply h.congr_right
  intro w
  change w⁻¹ * (w * w) = w
  by_cases hw : w = 0
  · simp [hw]
  · rw [← mul_assoc, inv_mul_cancel₀ hw, one_mul]

/-- Consequently the genuine correction is eventually norm smaller than one. -/
theorem multiplicative_centered_correction_eventually_norm_lt_one (a b : A)
    (ha : φ.expectation a ≠ 0) (hb : φ.expectation b ≠ 0) :
    ∀ᶠ w : ℂ in 𝓝 0, ‖(w * (1 + w))⁻¹ •
      (φ.toProbabilitySpace.center (Ring.inverse (1 - φ.momentInverse a ha w • a)) *
        φ.toProbabilitySpace.center (Ring.inverse (1 - φ.momentInverse b hb w • b)))‖ < 1 := by
  have ht := (φ.multiplicative_centered_correction_isBigO a b ha hb).trans_tendsto
    (tendsto_id : Filter.Tendsto (fun w : ℂ => w) (𝓝 0) (𝓝 0))
  exact ht.norm.eventually_lt tendsto_const_nhds (by simp)
end FreeProbability.StarProbabilitySpace

import FreeProbability.Analytic.Transform
import Mathlib.Tactic.Abel

/-! # Exact analytic transforms of idempotents

The inverse formula is algebraic and valid away from the pole. The selected
analytic inverse and S-transform formulas are equalities of germs at zero.
Their use for products of free projections still requires multiplicativity.
-/

namespace FreeProbability
variable {A : Type*} [Ring A] [Algebra ℂ A]

theorem inverse_one_sub_smul_idempotent (p : A) (hp : IsIdempotentElem p)
    (w : ℂ) (hw : w ≠ 1) :
    Ring.inverse (1 - w • p) = 1 + (w / (1 - w)) • p := by
  have hd : 1 - w ≠ 0 := sub_ne_zero.mpr hw.symm
  have hc : w / (1 - w) - w - w * (w / (1 - w)) = 0 := by
    field_simp
    ring
  have hl : (1 - w • p) * (1 + (w / (1 - w)) • p) = 1 := by
    calc
      _ = 1 + (w / (1 - w) - w - w * (w / (1 - w))) • p := by
        simp only [mul_add, sub_mul, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
          smul_smul, hp.eq, sub_smul, smul_sub, mul_comm]
        abel
      _ = 1 := by rw [hc]; simp
  have hr : (1 + (w / (1 - w)) • p) * (1 - w • p) = 1 := by
    calc
      _ = 1 + (w / (1 - w) - w - (w / (1 - w)) * w) • p := by
        simp only [add_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
          smul_smul, hp.eq, sub_smul, smul_add, mul_comm]
        abel
      _ = 1 := by rw [mul_comm (w / (1 - w)) w, hc]; simp
  let u : Aˣ := ⟨1 - w • p, 1 + (w / (1 - w)) • p, hl, hr⟩
  exact Ring.inverse_unit u

end FreeProbability

namespace FreeProbability.StarProbabilitySpace
open scoped Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (φ : FreeProbability.StarProbabilitySpace A)

omit [PartialOrder A] [StarOrderedRing A] in
theorem momentGeneratingFunction_idempotent (p : A) (hp : IsIdempotentElem p)
    (w : ℂ) (hw : w ≠ 1) :
    φ.momentGeneratingFunction p w = φ.expectation p * w / (1 - w) := by
  rw [momentGeneratingFunction, inverse_one_sub_smul_idempotent p hp w hw,
    map_add, map_smul, φ.map_one, smul_eq_mul]
  ring

omit [PartialOrder A] [StarOrderedRing A] in
theorem cauchyTransform_idempotent (p : A) (hp : IsIdempotentElem p)
    (z : ℂ) (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    φ.cauchyTransform p z = (1 - φ.expectation p) / z + φ.expectation p / (z - 1) := by
  have hi : z⁻¹ ≠ 1 := by
    intro hi
    apply hz1
    have hh := congrArg (fun t : ℂ => z * t) hi
    simpa only [mul_inv_cancel₀ hz0, mul_one] using hh.symm
  have hd : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  rw [φ.cauchyTransform_eq_scaled_inverse p z hz0,
    inverse_one_sub_smul_idempotent p hp z⁻¹ hi, map_add, map_smul, φ.map_one, smul_eq_mul]
  field_simp
  ring

theorem momentInverse_idempotent_eventually (p : A) (hp : IsIdempotentElem p)
    (h : φ.expectation p ≠ 0) :
    ∀ᶠ w in 𝓝 (0 : ℂ), φ.momentInverse p h w = w / (φ.expectation p + w) := by
  have hc : ∀ᶠ w in 𝓝 (0 : ℂ), φ.momentInverse p h w ≠ 1 :=
    (φ.analyticAt_momentInverse_zero p h).continuousAt.eventually_ne (by simp)
  have hd : ∀ᶠ w in 𝓝 (0 : ℂ), φ.expectation p + w ≠ 0 :=
    (continuous_const.add continuous_id).continuousAt.eventually_ne (by simpa only [Pi.add_apply, id_eq, add_zero] using h)
  filter_upwards [φ.momentInverse_eventually_right_inverse p h, hc, hd] with w hw hc hd
  rw [φ.momentGeneratingFunction_idempotent p hp _ hc] at hw
  have hn : 1 - φ.momentInverse p h w ≠ 0 := sub_ne_zero.mpr hc.symm
  have he := (div_eq_iff hn).mp hw
  apply (eq_div_iff hd).mpr
  calc
    _ = φ.expectation p * φ.momentInverse p h w + w * φ.momentInverse p h w := by ring
    _ = w * (1 - φ.momentInverse p h w) + w * φ.momentInverse p h w := by rw [he]
    _ = w := by ring

theorem sTransform_idempotent_eventually (p : A) (hp : IsIdempotentElem p)
    (h : φ.expectation p ≠ 0) :
    ∀ᶠ w in 𝓝 (0 : ℂ), φ.sTransform p h w = (1 + w) / (φ.expectation p + w) := by
  filter_upwards [φ.momentInverse_idempotent_eventually p hp h] with w hw
  by_cases hz : w = 0
  · simp [hz]
  · rw [φ.sTransform_eq p h w hz, hw]
    field_simp

end FreeProbability.StarProbabilitySpace

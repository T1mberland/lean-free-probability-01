import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-! # Positive operator energy bound for directed monotone convergence -/
noncomputable section
open scoped InnerProductSpace
namespace FreeProbability
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The genuine Loewner-positive operator energy inequality on an arbitrary complete complex Hilbert space. -/
theorem positiveOperator_energy_le (D : H →L[ℂ] H) (hD : 0 ≤ D) (x : H) :
    ‖D x‖ ^ 2 ≤ ‖D‖ * (inner ℂ x (D x)).re := by
  let S := CFC.sqrt D
  have hS : IsSelfAdjoint S := .of_nonneg (CFC.sqrt_nonneg D)
  have hSS : S * S = D := CFC.sqrt_mul_sqrt_self D hD
  have hn : ‖S‖ ^ 2 = ‖D‖ := by
    rw [pow_two, ← CStarRing.norm_star_mul_self, hS.star_eq, hSS]
  have hi : ‖S x‖ ^ 2 = (inner ℂ x (D x)).re := by
    have ha := S.adjoint_inner_right x (S x)
    rw [← ContinuousLinearMap.star_eq_adjoint, hS.star_eq] at ha
    have hm : S (S x) = D x := by
      change (S * S) x = D x
      rw [hSS]
    rw [hm, inner_self_eq_norm_sq_to_K] at ha
    simpa only [RCLike.re_ofReal_pow, RCLike.re_eq_complex_re] using (congrArg RCLike.re ha).symm
  have hb := S.le_opNorm (S x)
  have hc : ‖D x‖ ≤ ‖S‖ * ‖S x‖ := by
    change ‖(S * S) x‖ ≤ _ at hb
    rwa [hSS] at hb
  calc
    ‖D x‖ ^ 2 ≤ (‖S‖ * ‖S x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hc 2
    _ = ‖S‖ ^ 2 * ‖S x‖ ^ 2 := mul_pow _ _ _
    _ = _ := by rw [hn, hi]
end FreeProbability

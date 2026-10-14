import FreeProbability.OperatorValued.OperatorGeometricResolventComparison
import FreeProbability.OperatorValued.OperatorRetainedPowers
import Mathlib.Algebra.Algebra.Spectrum.Basic

/-! # Actual scaled resolvent tails for sandwich compressions -/
noncomputable section
open scoped Ring
namespace FreeProbability
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem operator_scaled_inverse (A : E →L[ℂ] E) (d : ℝ) (hd : d ≠ 0) :
    ((d : ℂ) • 1 - A)⁻¹ʳ = (d : ℂ)⁻¹ • (1 - (d : ℂ)⁻¹ • A)⁻¹ʳ := by
  have hc : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have h := spectrum.units_smul_resolvent
    (r := Units.mk0 (d : ℂ) hc) (s := (d : ℂ)) (a := A)
  have hh : (d : ℂ) • ((d : ℂ) • 1 - A)⁻¹ʳ =
      (1 - (d : ℂ)⁻¹ • A)⁻¹ʳ := by
    simpa [resolvent, Algebra.algebraMap_eq_smul_one, Units.smul_def, hc] using h
  rw [← hh, inv_smul_smul₀ hc]

/-- The actual inverses, not a formal series, obey a geometric tail bound on retained vectors. -/
theorem scaledInverse_sandwich_comparison (Q A : E →L[ℂ] E) (R d : ℝ)
    (hR : 0 ≤ R) (hd : R < d) (hA : ‖A‖ ≤ R) (hQ : ‖Q‖ ≤ 1)
    (L : ℕ) (x : E) (hp : ∀ k ≤ L, Q ((A ^ k) x) = (A ^ k) x) :
    ‖((d : ℂ) • 1 - A)⁻¹ʳ x - ((d : ℂ) • 1 - Q * A * Q)⁻¹ʳ x‖ ≤
      2 * (R / d) ^ (L + 1) / (d - R) * ‖x‖ := by
  have hd0 : 0 < d := hR.trans_lt hd
  have hc : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
  have hB : ‖Q * A * Q‖ ≤ R := by
    calc
      _ ≤ ‖Q‖ * ‖A‖ * ‖Q‖ := (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ 1 * R * 1 := by gcongr
      _ = R := by ring
  have hn (T : E →L[ℂ] E) (hT : ‖T‖ ≤ R) : ‖(d : ℂ)⁻¹ • T‖ ≤ R / d := by
    calc
      _ ≤ ‖(d : ℂ)⁻¹‖ * ‖T‖ := ContinuousLinearMap.opNorm_smul_le _ _
      _ ≤ d⁻¹ * R := by
        rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hd0.le]
        exact mul_le_mul_of_nonneg_left hT (inv_nonneg.mpr hd0.le)
      _ = R / d := by ring
  have hp' : ∀ k ≤ L, (((d : ℂ)⁻¹ • A) ^ k) x =
      (((d : ℂ)⁻¹ • (Q * A * Q)) ^ k) x := by
    intro k hk
    rw [smul_pow, smul_pow, smul_apply, smul_apply,
      operator_sandwich_pow_apply_eq Q A L x hp k hk]
  have hh := geometricInverse_apply_comparison ((d : ℂ)⁻¹ • A)
    ((d : ℂ)⁻¹ • (Q * A * Q)) (R / d) (div_nonneg hR hd0.le)
    ((div_lt_one hd0).mpr hd) (hn A hA) (hn _ hB) L x hp'
  rw [operator_scaled_inverse A d hd0.ne', operator_scaled_inverse (Q * A * Q) d hd0.ne',
    smul_apply, smul_apply, ← smul_sub, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg hd0.le]
  calc
    _ ≤ d⁻¹ * (2 * (R / d) ^ (L + 1) / (1 - R / d) * ‖x‖) :=
      mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hd0.le)
    _ = _ := by field_simp

end FreeProbability

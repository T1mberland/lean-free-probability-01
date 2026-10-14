import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp

/-! # Actual multiplicative resolvent factorization

Unit transport uses both invertible outer factors and never infers invertibility
from a one-sided inverse in a general noncommutative algebra.
-/

noncomputable section
namespace FreeProbability
variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]

/-- An actual invertible sandwich gives invertibility and the exact inverse,
without a finite-dimensional or directly-finite hypothesis. -/
theorem ringInverse_of_unit_sandwich (a b q r : A) (ha : IsUnit a) (hb : IsUnit b)
    (hr : IsUnit r) (h : a * q * b = r) :
    IsUnit q ∧ Ring.inverse q = b * Ring.inverse r * a := by
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨v, rfl⟩ := hb
  obtain ⟨t, rfl⟩ := hr
  have hq : q = ((u⁻¹ * t * v⁻¹ : Aˣ) : A) := by
    calc
      q = (u⁻¹ : Aˣ) * ((u : A) * q * (v : A)) * (v⁻¹ : Aˣ) := by simp [mul_assoc]
      _ = _ := by rw [h]; rfl
  constructor
  · rw [hq]
    exact Units.isUnit _
  · rw [hq, Ring.inverse_unit, Ring.inverse_unit]
    simp only [mul_inv_rev, inv_inv, Units.val_mul, mul_assoc]

/-- The exact scaled algebraic identity for genuine scalar resolvents. -/
theorem multiplicative_resolvent_scaled_factorization (a b : A) (s t w γ : 𝕜)
    (hs : IsUnit (1 - s • a)) (ht : IsUnit (1 - t • b))
    (hγ : w * γ = s * t * (1 + w)) :
    w • (Ring.inverse (1 - s • a) * (1 - γ • (a * b)) * Ring.inverse (1 - t • b)) =
      (w * (1 + w)) • (1 : A) -
        (Ring.inverse (1 - s • a) - (1 + w) • 1) *
        (Ring.inverse (1 - t • b) - (1 + w) • 1) := by
  let U := Ring.inverse (1 - s • a)
  let V := Ring.inverse (1 - t • b)
  have hUa : s • (U * a) = U - 1 := by
    have hc := Ring.inverse_mul_cancel (1 - s • a) hs
    change U * (1 - s • a) = 1 at hc
    rw [mul_sub, mul_one, mul_smul_comm] at hc
    exact (eq_sub_iff_add_eq).mpr (by rw [← hc]; abel)
  have hbV : t • (b * V) = V - 1 := by
    have hc := Ring.mul_inverse_cancel (1 - t • b) ht
    change (1 - t • b) * V = 1 at hc
    rw [sub_mul, one_mul, smul_mul_assoc] at hc
    exact (eq_sub_iff_add_eq).mpr (by rw [← hc]; abel)
  have hp : (s * t) • (U * (a * b) * V) = (U - 1) * (V - 1) := by
    rw [← hUa, ← hbV]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc, mul_comm s t]
  change w • (U * (1 - γ • (a * b)) * V) = _
  rw [mul_sub, mul_one, sub_mul, mul_smul_comm, smul_mul_assoc, smul_sub, smul_smul, hγ]
  have hscale : (s * t * (1 + w)) • (U * (a * b) * V) =
      (1 + w) • ((s * t) • (U * (a * b) * V)) := by
    rw [smul_smul]
    congr 1
    ring
  rw [hscale, hp]
  simp only [sub_mul, mul_sub, mul_one, one_mul, smul_sub,
    smul_mul_assoc, mul_smul_comm, smul_smul]
  module
/-- The exact unscaled factorization with its genuine scalar coefficient. -/
theorem multiplicative_resolvent_factorization (a b : A) (s t w : 𝕜)
    (hs : IsUnit (1 - s • a)) (ht : IsUnit (1 - t • b))
    (hw : w ≠ 0) (hc : 1 + w ≠ 0) :
    Ring.inverse (1 - s • a) * (1 - (s * t * (1 + w) / w) • (a * b)) *
        Ring.inverse (1 - t • b) =
      (1 + w) • (1 - (w * (1 + w))⁻¹ •
        ((Ring.inverse (1 - s • a) - (1 + w) • 1) *
          (Ring.inverse (1 - t • b) - (1 + w) • 1))) := by
  have hγ : w * (s * t * (1 + w) / w) = s * t * (1 + w) := by field_simp
  have h := congrArg (fun x : A => w⁻¹ • x)
    (multiplicative_resolvent_scaled_factorization a b s t w _ hs ht hγ)
  simp only [smul_sub, smul_smul, inv_mul_cancel₀ hw, one_smul] at h
  have hk : w⁻¹ * (w * (1 + w)) = 1 + w := by field_simp
  have hk' : (1 + w) * (w * (1 + w))⁻¹ = w⁻¹ := by field_simp
  rw [hk] at h
  rw [smul_sub, smul_smul, hk']
  exact h

private theorem ringInverse_algebraMap_of_ne_zero (c : 𝕜) (hc : c ≠ 0) :
    Ring.inverse (algebraMap 𝕜 A c) = algebraMap 𝕜 A c⁻¹ := by
  have hu : IsUnit (algebraMap 𝕜 A c) := (isUnit_iff_ne_zero.mpr hc).map (algebraMap 𝕜 A)
  have h := (Ring.inverse_mul_eq_iff_eq_mul (algebraMap 𝕜 A c) 1
    (algebraMap 𝕜 A c⁻¹) hu).mpr (by rw [← map_mul, mul_inv_cancel₀ hc, map_one])
  simpa only [mul_one] using h

/-- The actual inverse of a nonzero scalar multiple, in a general algebra. -/
theorem ringInverse_smul_of_ne_zero (c : 𝕜) (hc : c ≠ 0) (a : A) :
    Ring.inverse (c • a) = c⁻¹ • Ring.inverse a := by
  have hu : IsUnit (algebraMap 𝕜 A c) := (isUnit_iff_ne_zero.mpr hc).map (algebraMap 𝕜 A)
  rw [Algebra.smul_def, Ring.inverse_mul (Or.inl hu), ringInverse_algebraMap_of_ne_zero c hc]
  simp only [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]

/-- The genuine product resolvent is invertible and has the exact factored
inverse when the centered correction is invertible. -/
theorem multiplicative_resolvent_inverse (a b : A) (s t w : 𝕜)
    (hs : IsUnit (1 - s • a)) (ht : IsUnit (1 - t • b))
    (hw : w ≠ 0) (hc : 1 + w ≠ 0)
    (hT : IsUnit (1 - (w * (1 + w))⁻¹ •
      ((Ring.inverse (1 - s • a) - (1 + w) • 1) *
        (Ring.inverse (1 - t • b) - (1 + w) • 1)))) :
    IsUnit (1 - (s * t * (1 + w) / w) • (a * b)) ∧
      Ring.inverse (1 - (s * t * (1 + w) / w) • (a * b)) =
        Ring.inverse (1 - t • b) * ((1 + w)⁻¹ •
          Ring.inverse (1 - (w * (1 + w))⁻¹ •
            ((Ring.inverse (1 - s • a) - (1 + w) • 1) *
              (Ring.inverse (1 - t • b) - (1 + w) • 1)))) * Ring.inverse (1 - s • a) := by
  have hcu : IsUnit (algebraMap 𝕜 A (1 + w)) :=
    (isUnit_iff_ne_zero.mpr hc).map (algebraMap 𝕜 A)
  have hr := hcu.mul hT
  rw [← Algebra.smul_def] at hr
  have h := ringInverse_of_unit_sandwich _ _ _ _ hs.ringInverse ht.ringInverse hr
    (multiplicative_resolvent_factorization a b s t w hs ht hw hc)
  rw [ringInverse_smul_of_ne_zero _ hc] at h
  exact h
end FreeProbability

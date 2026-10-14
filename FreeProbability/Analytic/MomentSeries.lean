import FreeProbability.Analytic.Expectation
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-! # Actual resolvent expectations and convergent moment expansions -/

namespace FreeProbability.StarProbabilitySpace

open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (φ : FreeProbability.StarProbabilitySpace A)

noncomputable def momentGeneratingFunction (a : A) (w : ℂ) : ℂ :=
  φ.expectation (Ring.inverse (1 - w • a)) - 1

noncomputable def cauchyTransform (a : A) (z : ℂ) : ℂ :=
  φ.expectation (resolvent a z)

/-- The inverse expectation is the actual convergent moment series near zero. -/
theorem hasSum_expectation_inverse (a : A) (w : ℂ) (h : ‖w‖ * ‖a‖ < 1) :
    HasSum (fun k : ℕ => w ^ k * φ.expectation (a ^ k))
      (φ.expectation (Ring.inverse (1 - w • a))) := by
  let _ : Nontrivial A := φ.toProbabilitySpace.nontrivial
  have hn : ‖w • a‖ < 1 := by simpa only [norm_smul] using h
  have hs := φ.continuousExpectation.hasSum (hasSum_geom_series_inverse (w • a) hn)
  simpa only [smul_pow, continuousExpectation_apply, map_smul, smul_eq_mul] using hs

/-- Removing the normalized zeroth moment gives the convergent series for
the actual moment-generating function. -/
theorem hasSum_momentGeneratingFunction (a : A) (w : ℂ) (h : ‖w‖ * ‖a‖ < 1) :
    HasSum (fun k : ℕ => w ^ (k + 1) * φ.expectation (a ^ (k + 1)))
      (φ.momentGeneratingFunction a w) := by
  have hs := (hasSum_nat_add_iff' 1).mpr (φ.hasSum_expectation_inverse a w h)
  simpa only [Finset.sum_range_one, pow_zero, φ.map_one, one_mul,
    momentGeneratingFunction] using hs

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem momentGeneratingFunction_zero (a : A) : φ.momentGeneratingFunction a 0 = 0 := by
  simp [momentGeneratingFunction, φ.map_one]

omit [PartialOrder A] [StarOrderedRing A] in
theorem cauchyTransform_eq_scaled_inverse (a : A) (z : ℂ) (hz : z ≠ 0) :
    φ.cauchyTransform a z = z⁻¹ * φ.expectation (Ring.inverse (1 - z⁻¹ • a)) := by
  have h := congrArg φ.expectation
    (spectrum.units_smul_resolvent_self (r := Units.mk0 z hz) (a := a))
  simp only [Units.smul_def, Units.val_mk0, Units.val_inv_eq_inv_val, map_smul, smul_eq_mul,
    resolvent, map_one] at h
  change z * φ.cauchyTransform a z = φ.expectation (Ring.inverse (1 - z⁻¹ • a)) at h
  rw [← h]
  rw [← mul_assoc, inv_mul_cancel₀ hz, one_mul]

/-- The Cauchy transform is defined by the genuine algebra resolvent and equals
its moment Laurent series throughout the exterior norm region. -/
theorem hasSum_cauchyTransform (a : A) (z : ℂ) (hz : ‖a‖ < ‖z‖) :
    HasSum (fun k : ℕ => φ.expectation (a ^ k) / z ^ (k + 1)) (φ.cauchyTransform a z) := by
  have hn : 0 < ‖z‖ := (norm_nonneg a).trans_lt hz
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp hn.ne'
  have hi : ‖z⁻¹‖ * ‖a‖ < 1 := by
    rw [norm_inv, ← div_eq_inv_mul]
    exact (div_lt_one hn).mpr hz
  have hs := (φ.hasSum_expectation_inverse a z⁻¹ hi).mul_left z⁻¹
  have he (k : ℕ) : z⁻¹ * (z⁻¹ ^ k * φ.expectation (a ^ k)) =
      φ.expectation (a ^ k) / z ^ (k + 1) := by
    simp only [inv_pow, pow_succ, mul_inv_rev, div_eq_mul_inv]
    ring
  rw [← φ.cauchyTransform_eq_scaled_inverse a z hz0] at hs
  simpa only [he] using hs

/-- The usual exterior Cauchy-transform bound follows from positivity and
the convergent geometric majorant. -/
theorem cauchyTransform_norm_le (a : A) (z : ℂ) (hz : ‖a‖ < ‖z‖) :
    ‖φ.cauchyTransform a z‖ ≤ 1 / (‖z‖ - ‖a‖) := by
  have hn : 0 < ‖z‖ := (norm_nonneg a).trans_lt hz
  have hq : ‖a‖ / ‖z‖ < 1 := (div_lt_one hn).mpr hz
  have hg := (hasSum_geometric_of_lt_one
    (div_nonneg (norm_nonneg a) (norm_nonneg z)) hq).mul_left (1 / ‖z‖)
  have he : (1 / ‖z‖) * (1 - ‖a‖ / ‖z‖)⁻¹ = 1 / (‖z‖ - ‖a‖) := by
    field_simp
  rw [he] at hg
  apply (φ.hasSum_cauchyTransform a z hz).norm_le_of_bounded hg
  intro k
  rw [norm_div, norm_pow]
  calc
    ‖φ.expectation (a ^ k)‖ / ‖z‖ ^ (k + 1) ≤ ‖a‖ ^ k / ‖z‖ ^ (k + 1) :=
      div_le_div_of_nonneg_right (φ.expectation_pow_norm_le a k) (pow_nonneg hn.le _)
    _ = (1 / ‖z‖) * (‖a‖ / ‖z‖) ^ k := by
      rw [div_pow, pow_succ]
      field_simp

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- Power moments determine the actual Cauchy transforms in their common
exterior region, even for variables in different ambient algebras. -/
theorem cauchyTransform_eq_of_powerMoments (ψ : FreeProbability.StarProbabilitySpace B)
    (a : A) (b : B) (h : ∀ k : ℕ, φ.expectation (a ^ k) = ψ.expectation (b ^ k))
    (z : ℂ) (ha : ‖a‖ < ‖z‖) (hb : ‖b‖ < ‖z‖) :
    φ.cauchyTransform a z = ψ.cauchyTransform b z := by
  have hs := φ.hasSum_cauchyTransform a z ha
  have ht := ψ.hasSum_cauchyTransform b z hb
  have he : (fun k : ℕ => φ.expectation (a ^ k) / z ^ (k + 1)) =
      (fun k : ℕ => ψ.expectation (b ^ k) / z ^ (k + 1)) := by
    funext k
    rw [h k]
  rw [he] at hs
  exact hs.unique ht

theorem momentGeneratingFunction_eq_of_powerMoments (ψ : FreeProbability.StarProbabilitySpace B)
    (a : A) (b : B) (h : ∀ k : ℕ, φ.expectation (a ^ k) = ψ.expectation (b ^ k))
    (w : ℂ) (ha : ‖w‖ * ‖a‖ < 1) (hb : ‖w‖ * ‖b‖ < 1) :
    φ.momentGeneratingFunction a w = ψ.momentGeneratingFunction b w := by
  have hs := φ.hasSum_expectation_inverse a w ha
  have ht := ψ.hasSum_expectation_inverse b w hb
  have he : (fun k : ℕ => w ^ k * φ.expectation (a ^ k)) =
      (fun k : ℕ => w ^ k * ψ.expectation (b ^ k)) := by
    funext k
    rw [h k]
  rw [he] at hs
  exact congrArg (fun v : ℂ => v - 1) (hs.unique ht)

end FreeProbability.StarProbabilitySpace

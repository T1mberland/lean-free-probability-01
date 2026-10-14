import FreeProbability.Algebraic.FreenessClosureResolvent
import Mathlib.Analysis.Normed.Operator.Basic

/-! # Quantitative actual near-identity inverse bounds -/

noncomputable section
open scoped Topology
namespace FreeProbability
variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
    [CompleteSpace A]

/-- Removing the zeroth term gives the true geometric remainder estimate,
even when the norm of the unit is not one. -/
theorem norm_inverse_one_sub_sub_one_le (x : A) (hx : ‖x‖ < 1) :
    ‖Ring.inverse (1 - x) - 1‖ ≤ ‖x‖ / (1 - ‖x‖) := by
  have hs := (hasSum_nat_add_iff' 1).mpr (hasSum_geom_series_inverse x hx)
  have htail : HasSum (fun k : ℕ => x ^ (k + 1)) (Ring.inverse (1 - x) - 1) := by
    simpa only [Finset.sum_range_one, pow_zero] using hs
  have hg := (hasSum_geometric_of_lt_one (norm_nonneg x) hx).mul_left ‖x‖
  have hreal : HasSum (fun k : ℕ => ‖x‖ ^ (k + 1)) (‖x‖ / (1 - ‖x‖)) := by
    simpa only [pow_succ', div_eq_mul_inv] using hg
  exact htail.norm_le_of_bounded hreal (fun k => norm_pow_le' x (by omega))

namespace ProbabilitySpace
/-- A continuous algebraic expectation, bundled without positivity assumptions. -/
def continuousLinearExpectation (φ : ProbabilitySpace 𝕜 A) (hφ : Continuous φ.expectation) :
    A →L[𝕜] 𝕜 where
  toLinearMap := φ.expectation
  cont := hφ

omit [CompleteSpace A] in
@[simp] theorem continuousLinearExpectation_apply (φ : ProbabilitySpace 𝕜 A)
    (hφ : Continuous φ.expectation) (x : A) :
    φ.continuousLinearExpectation hφ x = φ.expectation x := rfl

/-- Quantitative centering bound for a true inverse, for every continuous
normalized expectation on a Banach algebra. -/
theorem norm_center_inverse_one_sub_le (φ : ProbabilitySpace 𝕜 A)
    (hφ : Continuous φ.expectation) (x : A) (hx : ‖x‖ < 1) :
    ‖φ.center (Ring.inverse (1 - x))‖ ≤
      (1 + ‖φ.continuousLinearExpectation hφ‖ * ‖(1 : A)‖) * ‖x‖ / (1 - ‖x‖) := by
  let r := Ring.inverse (1 - x) - 1
  have heq : φ.center (Ring.inverse (1 - x)) = r - φ.expectation r • (1 : A) := by
    simp only [r, center, map_sub, φ.expectation_one, Algebra.algebraMap_eq_smul_one,
      sub_smul, one_smul]
    abel
  have hnorm := (φ.continuousLinearExpectation hφ).le_opNorm r
  have hc : ‖φ.center (Ring.inverse (1 - x))‖ ≤
      (1 + ‖φ.continuousLinearExpectation hφ‖ * ‖(1 : A)‖) * ‖r‖ := by
    rw [heq]
    calc
      ‖r - φ.expectation r • (1 : A)‖ ≤ ‖r‖ + ‖φ.expectation r • (1 : A)‖ := norm_sub_le _ _
      _ = ‖r‖ + ‖φ.expectation r‖ * ‖(1 : A)‖ := by rw [norm_smul]
      _ ≤ ‖r‖ + (‖φ.continuousLinearExpectation hφ‖ * ‖r‖) * ‖(1 : A)‖ := by
        gcongr
        exact hnorm
      _ = (1 + ‖φ.continuousLinearExpectation hφ‖ * ‖(1 : A)‖) * ‖r‖ := by ring
  calc
    _ ≤ (1 + ‖φ.continuousLinearExpectation hφ‖ * ‖(1 : A)‖) * ‖r‖ := hc
    _ ≤ (1 + ‖φ.continuousLinearExpectation hφ‖ * ‖(1 : A)‖) * (‖x‖ / (1 - ‖x‖)) := by
      gcongr
      exact norm_inverse_one_sub_sub_one_le x hx
    _ = _ := by ring
/-- An explicit uniform linear estimate in the half-unit neighborhood. -/
theorem norm_center_inverse_one_sub_le_of_norm_le_half (φ : ProbabilitySpace 𝕜 A)
    (hφ : Continuous φ.expectation) (x : A) (hx : ‖x‖ ≤ 1 / 2) :
    ‖φ.center (Ring.inverse (1 - x))‖ ≤
      2 * (1 + ‖φ.continuousLinearExpectation hφ‖ * ‖(1 : A)‖) * ‖x‖ := by
  have hx1 : ‖x‖ < 1 := by linarith
  have hd : ‖x‖ / (1 - ‖x‖) ≤ 2 * ‖x‖ := by
    apply (div_le_iff₀ (sub_pos.mpr hx1)).mpr
    nlinarith [norm_nonneg x]
  calc
    _ ≤ (1 + ‖φ.continuousLinearExpectation hφ‖ * ‖(1 : A)‖) *
        (‖x‖ / (1 - ‖x‖)) := by
      simpa only [mul_div_assoc] using φ.norm_center_inverse_one_sub_le hφ x hx1
    _ ≤ (1 + ‖φ.continuousLinearExpectation hφ‖ * ‖(1 : A)‖) * (2 * ‖x‖) := by
      gcongr
    _ = _ := by ring

/-- The actual centered inverse is O(z) at zero, from the proved quantitative
Neumann remainder and bounded continuous expectation. -/
theorem center_inverse_one_sub_smul_isBigO (φ : ProbabilitySpace 𝕜 A)
    (hφ : Continuous φ.expectation) (a : A) :
    (fun z : 𝕜 => φ.center (Ring.inverse (1 - z • a))) =O[𝓝 0] (fun z : 𝕜 => z) := by
  apply Asymptotics.IsBigO.of_bound
    (2 * (1 + ‖φ.continuousLinearExpectation hφ‖ * ‖(1 : A)‖) * ‖a‖)
  have hq : {z : 𝕜 | ‖z • a‖ < 1 / 2} ∈ 𝓝 0 :=
    (isOpen_lt (continuous_id.smul continuous_const).norm continuous_const).mem_nhds (by simp)
  filter_upwards [hq] with z hz
  have h := φ.norm_center_inverse_one_sub_le_of_norm_le_half hφ (z • a) hz.le
  simpa only [norm_smul, mul_assoc, mul_comm ‖a‖ ‖z‖] using h
end ProbabilitySpace
end FreeProbability

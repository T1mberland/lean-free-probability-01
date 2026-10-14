import FreeProbability.Analytic.MultiplicativeResolventS
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-! # Actual positive sandwich S-transform for given free positive elements -/

noncomputable section
open scoped Topology
namespace FreeProbability
namespace IsTracial
variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A] {φ : ProbabilitySpace 𝕜 A}

/-- A genuine trace is cyclic on all powers of two-factor products. -/
theorem expectation_pow_mul (hφ : IsTracial φ) (a b : A) (n : ℕ) :
    φ.expectation ((a * b) ^ n) = φ.expectation ((b * a) ^ n) := by
  cases n with
  | zero => simp only [pow_zero]
  | succ n =>
    rw [pow_succ, ← mul_assoc, mul_pow_mul, hφ (a * (b * a) ^ n) b,
      ← mul_assoc, ← pow_succ']

/-- Literal sandwich powers and the corresponding product powers have the
same trace; no commutation or invertibility is required. -/
theorem expectation_pow_sandwich (hφ : IsTracial φ) (s b : A) (n : ℕ) :
    φ.expectation ((s * b * s) ^ n) = φ.expectation (((s * s) * b) ^ n) := by
  rw [mul_assoc s b s, hφ.expectation_pow_mul s (b * s) n,
    mul_assoc b s s, hφ.expectation_pow_mul b (s * s) n]
end IsTracial

variable {A I : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The actual positive multiplication model of two given positive elements. -/
def positiveMultiplicativeSandwich (a b : A) : A := CFC.sqrt a * b * CFC.sqrt a

/-- The actual square-root sandwich is positive without coefficient commutation. -/
theorem positiveMultiplicativeSandwich_nonneg (a b : A) (hb : 0 ≤ b) :
    0 ≤ positiveMultiplicativeSandwich a b := by
  have hs : IsSelfAdjoint (CFC.sqrt a) := (CFC.sqrt_nonneg a).isSelfAdjoint
  simpa only [hs.star_eq, positiveMultiplicativeSandwich] using star_left_conjugate_nonneg hb (CFC.sqrt a)

namespace StarProbabilitySpace
variable (φ : FreeProbability.StarProbabilitySpace A)

/-- The actual positive sandwich has the exact product power moments under a
tracial state. -/
theorem expectation_pow_positiveMultiplicativeSandwich
    (hφ : IsTracial φ.toProbabilitySpace) (a b : A) (ha : 0 ≤ a) (n : ℕ) :
    φ.expectation (positiveMultiplicativeSandwich a b ^ n) = φ.expectation ((a * b) ^ n) := by
  have h := hφ.expectation_pow_sandwich (CFC.sqrt a) b n
  rw [CFC.sqrt_mul_sqrt_self a ha] at h
  exact h

/-- The sandwich first moment is nonzero by actual free factorization. -/
theorem expectation_positiveMultiplicativeSandwich_ne_zero
    (hφ : IsTracial φ.toProbabilitySpace) {B : I → Subalgebra ℂ A}
    (hf : FreelyIndependent φ.toProbabilitySpace B) {i j : I} (hij : i ≠ j)
    (a b : A) (ha : a ∈ B i) (hb : b ∈ B j) (hapos : 0 ≤ a)
    (hEa : φ.expectation a ≠ 0) (hEb : φ.expectation b ≠ 0) :
    φ.expectation (positiveMultiplicativeSandwich a b) ≠ 0 := by
  have h := φ.expectation_pow_positiveMultiplicativeSandwich hφ a b hapos 1
  simp only [pow_one] at h
  rw [h]
  exact hf.expectation_mul_ne_zero hij a b ha hb hEa hEb

/-- For any GIVEN free positive pair in a tracial C-star probability space,
the S-transform of its actual positive sandwich equals the product germ. -/
theorem sTransform_positiveMultiplicativeSandwich_eventually
    (hφ : IsTracial φ.toProbabilitySpace) {B : I → Subalgebra ℂ A}
    (hf : FreelyIndependent φ.toProbabilitySpace B) {i j : I} (hij : i ≠ j)
    (a b : A) (ha : a ∈ B i) (hb : b ∈ B j) (hapos : 0 ≤ a)
    (hEa : φ.expectation a ≠ 0) (hEb : φ.expectation b ≠ 0) :
    φ.sTransform (positiveMultiplicativeSandwich a b)
      (φ.expectation_positiveMultiplicativeSandwich_ne_zero hφ hf hij a b ha hb hapos hEa hEb)
      =ᶠ[𝓝 0] (fun w => φ.sTransform a hEa w * φ.sTransform b hEb w) := by
  exact (φ.sTransform_eventually_eq_of_powerMoments φ _ _
    (φ.expectation_pow_positiveMultiplicativeSandwich hφ a b hapos) _
    (hf.expectation_mul_ne_zero hij a b ha hb hEa hEb)).trans
      (φ.sTransform_mul_eventually hf hij a b ha hb hEa hEb)
end StarProbabilitySpace
end FreeProbability

import FreeProbability.Analytic.MultiplicativeResolventExpectation
import FreeProbability.Analytic.MultiplicativeResolventGermBounds
import FreeProbability.Analytic.TransformNaturality

/-! # Actual analytic S-transform multiplicativity under freeness

The identity is proved for the given elements in their actual C-star probability
space. No multiplicative transform or moment identity is supplied as a premise.
-/

noncomputable section
open scoped Topology
open Filter
namespace FreeProbability

variable {A I : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
/-- Nonzero marginal first moments give a nonzero product first moment by
actual freeness. -/
theorem FreelyIndependent.expectation_mul_ne_zero {φ : ProbabilitySpace ℂ A}
    {B : I → Subalgebra ℂ A} (hf : FreelyIndependent φ B) {i j : I} (hij : i ≠ j)
    (a b : A) (ha : a ∈ B i) (hb : b ∈ B j)
    (hEa : φ.expectation a ≠ 0) (hEb : φ.expectation b ≠ 0) :
    φ.expectation (a * b) ≠ 0 := by
  rw [hf.expectation_mul hij ha hb]
  exact mul_ne_zero hEa hEb

namespace StarProbabilitySpace
variable (φ : FreeProbability.StarProbabilitySpace A)

/-- The continuous candidate for the actual product moment inverse. -/
def multiplicativeInverseCandidate (a b : A) (ha : φ.expectation a ≠ 0)
    (hb : φ.expectation b ≠ 0) (w : ℂ) : ℂ :=
  w / (1 + w) * φ.sTransform a ha w * φ.sTransform b hb w

@[simp] theorem multiplicativeInverseCandidate_zero (a b : A)
    (ha : φ.expectation a ≠ 0) (hb : φ.expectation b ≠ 0) :
    φ.multiplicativeInverseCandidate a b ha hb 0 = 0 := by simp [multiplicativeInverseCandidate]

theorem multiplicativeInverseCandidate_continuousAt_zero (a b : A)
    (ha : φ.expectation a ≠ 0) (hb : φ.expectation b ≠ 0) :
    ContinuousAt (φ.multiplicativeInverseCandidate a b ha hb) 0 :=
  ((continuousAt_id.div (continuousAt_const.add continuousAt_id) (by simp)).mul
    (φ.analyticAt_sTransform_zero a ha).continuousAt).mul
      (φ.analyticAt_sTransform_zero b hb).continuousAt

theorem multiplicativeInverseCandidate_eq (a b : A)
    (ha : φ.expectation a ≠ 0) (hb : φ.expectation b ≠ 0)
    (w : ℂ) (hw : w ≠ 0) (hc : 1 + w ≠ 0) :
    φ.multiplicativeInverseCandidate a b ha hb w =
      φ.momentInverse a ha w * φ.momentInverse b hb w * (1 + w) / w := by
  rw [multiplicativeInverseCandidate, φ.sTransform_eq a ha w hw, φ.sTransform_eq b hb w hw]
  field_simp

/-- The candidate is an actual right inverse of the product moment-generating
function near zero; all Neumann and centering hypotheses are discharged. -/
theorem momentGeneratingFunction_multiplicativeInverseCandidate_eventually
    {B : I → Subalgebra ℂ A} (hf : FreelyIndependent φ.toProbabilitySpace B)
    {i j : I} (hij : i ≠ j) (a b : A) (ha : a ∈ B i) (hb : b ∈ B j)
    (hEa : φ.expectation a ≠ 0) (hEb : φ.expectation b ≠ 0) :
    ∀ᶠ w : ℂ in 𝓝 0,
      φ.momentGeneratingFunction (a * b) (φ.multiplicativeInverseCandidate a b hEa hEb w) = w := by
  have hs : ∀ᶠ w : ℂ in 𝓝 0, ‖φ.momentInverse a hEa w • a‖ < 1 :=
    ((φ.analyticAt_momentInverse_zero a hEa).continuousAt.smul_const a).norm.eventually_lt
      continuousAt_const (by simp)
  have ht : ∀ᶠ w : ℂ in 𝓝 0, ‖φ.momentInverse b hEb w • b‖ < 1 :=
    ((φ.analyticAt_momentInverse_zero b hEb).continuousAt.smul_const b).norm.eventually_lt
      continuousAt_const (by simp)
  have hc : ∀ᶠ w : ℂ in 𝓝 0, 1 + w ≠ 0 :=
    (isOpen_ne.preimage (continuous_const.add continuous_id)).mem_nhds (by simp)
  filter_upwards [hs, ht, hc, φ.momentInverse_eventually_right_inverse a hEa,
    φ.momentInverse_eventually_right_inverse b hEb,
    φ.multiplicative_centered_correction_eventually_norm_lt_one a b hEa hEb]
    with w hs ht hc hsa htb hT
  by_cases hw : w = 0
  · simp [hw]
  have hEs : φ.expectation (Ring.inverse (1 - φ.momentInverse a hEa w • a)) = 1 + w := by
    change φ.expectation _ - 1 = w at hsa
    simpa only [add_comm] using sub_eq_iff_eq_add.mp hsa
  have hEt : φ.expectation (Ring.inverse (1 - φ.momentInverse b hEb w • b)) = 1 + w := by
    change φ.expectation _ - 1 = w at htb
    simpa only [add_comm] using sub_eq_iff_eq_add.mp htb
  have hca : φ.toProbabilitySpace.center (Ring.inverse (1 - φ.momentInverse a hEa w • a)) =
      Ring.inverse (1 - φ.momentInverse a hEa w • a) - (1 + w) • 1 := by
    rw [ProbabilitySpace.center, hEs, Algebra.algebraMap_eq_smul_one]
  have hcb : φ.toProbabilitySpace.center (Ring.inverse (1 - φ.momentInverse b hEb w • b)) =
      Ring.inverse (1 - φ.momentInverse b hEb w • b) - (1 + w) • 1 := by
    rw [ProbabilitySpace.center, hEt, Algebra.algebraMap_eq_smul_one]
  rw [hca, hcb] at hT
  have h := hf.expectation_multiplicative_resolvent φ.continuous_expectation hij a b ha hb
    (φ.momentInverse a hEa w) (φ.momentInverse b hEb w) w hs ht hw hc hEs hEt hT
  rw [φ.multiplicativeInverseCandidate_eq a b hEa hEb w hw hc]
  change φ.expectation _ - 1 = w
  rw [h]
  ring

/-- The actual product inverse moment germ has the multiplicative candidate. -/
theorem momentInverse_mul_eventually
    {B : I → Subalgebra ℂ A} (hf : FreelyIndependent φ.toProbabilitySpace B)
    {i j : I} (hij : i ≠ j) (a b : A) (ha : a ∈ B i) (hb : b ∈ B j)
    (hEa : φ.expectation a ≠ 0) (hEb : φ.expectation b ≠ 0) :
    φ.momentInverse (a * b) (hf.expectation_mul_ne_zero hij a b ha hb hEa hEb) =ᶠ[𝓝 0]
      φ.multiplicativeInverseCandidate a b hEa hEb :=
  φ.momentInverse_eq_of_eventually_right_inverse _ _ _
    (φ.multiplicativeInverseCandidate_continuousAt_zero a b hEa hEb)
    (φ.multiplicativeInverseCandidate_zero a b hEa hEb)
    (φ.momentGeneratingFunction_multiplicativeInverseCandidate_eventually hf hij a b ha hb hEa hEb)

/-- Actual analytic S-transforms multiply for any two given free elements with
nonzero first moments, including their removable values at zero. -/
theorem sTransform_mul_eventually
    {B : I → Subalgebra ℂ A} (hf : FreelyIndependent φ.toProbabilitySpace B)
    {i j : I} (hij : i ≠ j) (a b : A) (ha : a ∈ B i) (hb : b ∈ B j)
    (hEa : φ.expectation a ≠ 0) (hEb : φ.expectation b ≠ 0) :
    φ.sTransform (a * b) (hf.expectation_mul_ne_zero hij a b ha hb hEa hEb) =ᶠ[𝓝 0]
      (fun w => φ.sTransform a hEa w * φ.sTransform b hEb w) := by
  have hc : ∀ᶠ w : ℂ in 𝓝 0, 1 + w ≠ 0 :=
    (isOpen_ne.preimage (continuous_const.add continuous_id)).mem_nhds (by simp)
  filter_upwards [φ.momentInverse_mul_eventually hf hij a b ha hb hEa hEb, hc] with w hw hc
  by_cases hz : w = 0
  · simp only [hz, φ.sTransform_zero, hf.expectation_mul hij ha hb, mul_inv_rev]
    exact mul_comm _ _
  · rw [φ.sTransform_eq _ _ w hz, hw, multiplicativeInverseCandidate]
    field_simp
end StarProbabilitySpace
end FreeProbability

import FreeProbability.Analytic.MultiplicativeResolventFactorization
import FreeProbability.Analytic.MultiplicativeResolventAlternating
import FreeProbability.Algebraic.FreenessClosureResolventBounds
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-! # Actual free product resolvent expectation

The correction is summed as a genuinely norm-convergent Neumann series.
The scalar mean hypotheses concern the two actual input resolvents.
-/

noncomputable section
namespace FreeProbability
variable {𝕜 A I : Type*} [NontriviallyNormedField 𝕜] [NormedRing A]
    [NormedAlgebra 𝕜 A] [CompleteSpace A]
namespace FreelyIndependent
variable {φ : ProbabilitySpace 𝕜 A} {B : I → Subalgebra 𝕜 A}

/-- The actual product resolvent expectation, from genuine freeness and a
convergent centered correction, without trace or positivity assumptions. -/
theorem expectation_multiplicative_resolvent (hf : FreelyIndependent φ B)
    (hφ : Continuous φ.expectation) {i j : I} (hij : i ≠ j)
    (a b : A) (ha : a ∈ B i) (hb : b ∈ B j) (s t w : 𝕜)
    (hs : ‖s • a‖ < 1) (ht : ‖t • b‖ < 1) (hw : w ≠ 0) (hc : 1 + w ≠ 0)
    (hEs : φ.expectation (Ring.inverse (1 - s • a)) = 1 + w)
    (hEt : φ.expectation (Ring.inverse (1 - t • b)) = 1 + w)
    (hT : ‖(w * (1 + w))⁻¹ •
      ((Ring.inverse (1 - s • a) - (1 + w) • 1) *
        (Ring.inverse (1 - t • b) - (1 + w) • 1))‖ < 1) :
    φ.expectation (Ring.inverse (1 - (s * t * (1 + w) / w) • (a * b))) = 1 + w := by
  let U := Ring.inverse (1 - s • a)
  let V := Ring.inverse (1 - t • b)
  let x := U - (1 + w) • 1
  let y := V - (1 + w) • 1
  let T := (w * (1 + w))⁻¹ • (x * y)
  have hxc : x = φ.center U := by rw [ProbabilitySpace.center, hEs, Algebra.algebraMap_eq_smul_one]
  have hyc : y = φ.center V := by rw [ProbabilitySpace.center, hEt, Algebra.algebraMap_eq_smul_one]
  have hxmem : x ∈ (B i).topologicalClosure := by
    rw [hxc]
    exact φ.center_mem _ (inverse_one_sub_smul_mem_topologicalClosure (B i) a ha s hs)
  have hymem : y ∈ (B j).topologicalClosure := by
    rw [hyc]
    exact φ.center_mem _ (inverse_one_sub_smul_mem_topologicalClosure (B j) b hb t ht)
  have hxzero : φ.expectation x = 0 := by rw [hxc]; exact φ.expectation_center _
  have hyzero : φ.expectation y = 0 := by rw [hyc]; exact φ.expectation_center _
  have hUc : U = x + (1 + w) • 1 := by dsimp [x]; abel
  have hVc : V = y + (1 + w) • 1 := by dsimp [y]; abel
  have hm (k : ℕ) : φ.expectation (V * T ^ k * U) =
      if k = 0 then (1 + w) * (1 + w) else 0 := by
    rw [hUc, hVc]
    simp only [T, smul_pow, mul_smul_comm, smul_mul_assoc, map_smul, smul_eq_mul]
    rw [(hf.topologicalClosure hφ).expectation_centered_pair_sandwich_pow hij x y
      hxmem hymem hxzero hyzero (1 + w) (1 + w) k]
    by_cases hk : k = 0
    · subst k
      simp
    · simp [hk]
  have hsE := (φ.continuousLinearExpectation hφ).hasSum
    (((hasSum_geom_series_inverse T hT).mul_left V).mul_right U)
  simp only [ProbabilitySpace.continuousLinearExpectation_apply, hm] at hsE
  have hex : φ.expectation (V * Ring.inverse (1 - T) * U) = (1 + w) * (1 + w) :=
    hsE.unique (hasSum_ite_eq 0 ((1 + w) * (1 + w)))
  have hInv := (multiplicative_resolvent_inverse a b s t w
    (isUnit_one_sub_of_norm_lt_one hs) (isUnit_one_sub_of_norm_lt_one ht) hw hc
    (isUnit_one_sub_of_norm_lt_one hT)).2
  rw [hInv]
  change φ.expectation (V * ((1 + w)⁻¹ • Ring.inverse (1 - T)) * U) = _
  rw [mul_smul_comm, smul_mul_assoc, map_smul, smul_eq_mul, hex]
  field_simp
end FreelyIndependent
end FreeProbability

import FreeProbability.Algebraic.FreenessClosureResolventBounds
import FreeProbability.Analytic.Expectation

/-! # Actual positive-state centered inverse bounds -/

namespace FreeProbability.StarProbabilitySpace
open scoped ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (φ : FreeProbability.StarProbabilitySpace A)

/-- Positivity and normalization give the universal factor two, without
supplying a norm-one or bounded-expectation premise. -/
theorem norm_center_inverse_one_sub_le (x : A) (hx : ‖x‖ < 1) :
    ‖φ.toProbabilitySpace.center (Ring.inverse (1 - x))‖ ≤ 2 * ‖x‖ / (1 - ‖x‖) := by
  let _ : Nontrivial A := φ.toProbabilitySpace.nontrivial
  have he : φ.toProbabilitySpace.continuousLinearExpectation φ.continuous_expectation =
      φ.continuousExpectation := by
    ext a
    rfl
  have h := φ.toProbabilitySpace.norm_center_inverse_one_sub_le φ.continuous_expectation x hx
  rw [he, φ.continuousExpectation_norm, norm_one] at h
  norm_num at h
  exact h

/-- The genuine centered inverse has a universal linear bound on the half-unit
ball, for every positive normalized C-star state. -/
theorem norm_center_inverse_one_sub_le_of_norm_le_half (x : A) (hx : ‖x‖ ≤ 1 / 2) :
    ‖φ.toProbabilitySpace.center (Ring.inverse (1 - x))‖ ≤ 4 * ‖x‖ := by
  have hx1 : ‖x‖ < 1 := by linarith
  have hd : 2 * ‖x‖ / (1 - ‖x‖) ≤ 4 * ‖x‖ := by
    apply (div_le_iff₀ (sub_pos.mpr hx1)).mpr
    nlinarith [norm_nonneg x]
  exact (φ.norm_center_inverse_one_sub_le x hx1).trans hd
end FreeProbability.StarProbabilitySpace

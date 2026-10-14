import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap

/-! # Positive complex-linear maps preserve the involution

Every element is a finite complex linear combination of genuine positive
operators. Positive maps send each of those operators to a self-adjoint one.
-/

namespace FreeProbability

variable {A B : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- Genuine star preservation for every positive complex-linear C-star map. -/
theorem positiveLinearMap_map_star (P : A →ₚ[ℂ] B) (T : A) : P (star T) = star (P T) := by
  obtain ⟨y, hy, _, hT⟩ := CStarAlgebra.exists_sum_four_nonneg T
  rw [hT, star_sum, map_sum, map_sum, star_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [star_smul, map_smul, (IsSelfAdjoint.of_nonneg (hy i)).star_eq,
    map_smul, star_smul, (IsSelfAdjoint.of_nonneg (map_nonneg P (hy i))).star_eq]

end FreeProbability

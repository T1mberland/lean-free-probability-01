import FreeProbability.Algebraic.StarProbabilitySpace
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The normalized matrix trace

Nonempty finite dimension and characteristic zero are explicit: otherwise the
normalizing factor can vanish and the trace need not be a normalized expectation.
Complex matrices give a positive, faithful, star-compatible tracial model.
-/

namespace FreeProbability

open scoped ComplexOrder
open Matrix

variable (𝕜 n : Type*) [Field 𝕜] [Fintype n]

/-- Normalized trace as a linear map. -/
noncomputable def normalizedTrace : Matrix n n 𝕜 →ₗ[𝕜] 𝕜 :=
  (Fintype.card n : 𝕜)⁻¹ • Matrix.traceLinearMap n 𝕜 𝕜

@[simp] theorem normalizedTrace_apply (M : Matrix n n 𝕜) :
    normalizedTrace 𝕜 n M = (Fintype.card n : 𝕜)⁻¹ * Matrix.trace M := rfl

variable [CharZero 𝕜] [Nonempty n]

theorem dimension_ne_zero : (Fintype.card n : 𝕜) ≠ 0 := by
  exact_mod_cast Fintype.card_ne_zero

variable [DecidableEq n]

@[simp] theorem normalizedTrace_one : normalizedTrace 𝕜 n 1 = 1 := by
  simp

/-- Every nonzero finite dimension gives an algebraic matrix probability space. -/
noncomputable def matrixProbabilitySpace : ProbabilitySpace 𝕜 (Matrix n n 𝕜) where
  expectation := normalizedTrace 𝕜 n
  map_one := normalizedTrace_one 𝕜 n

theorem matrixProbabilitySpace_isTracial : IsTracial (matrixProbabilitySpace 𝕜 n) := by
  intro M N
  simp only [matrixProbabilitySpace, normalizedTrace_apply, Matrix.trace_mul_comm M N]

variable {𝕜 n}

omit [CharZero 𝕜] [Nonempty n] [DecidableEq n] in
@[simp] theorem normalizedTrace_conjTranspose [StarRing 𝕜] (M : Matrix n n 𝕜) :
    normalizedTrace 𝕜 n Mᴴ = star (normalizedTrace 𝕜 n M) := by
  simp [star_mul, mul_comm]

variable (n)

omit [Nonempty n] [DecidableEq n] in
theorem normalizedTrace_star_mul_self_nonneg (M : Matrix n n ℂ) :
    0 ≤ normalizedTrace ℂ n (star M * M) := by
  rw [normalizedTrace_apply]
  apply mul_nonneg
  · have hr : 0 ≤ (Fintype.card n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
    simpa only [Complex.ofReal_inv, Complex.ofReal_natCast] using
      (Complex.zero_le_real.mpr hr)
  · exact (Matrix.posSemidef_conjTranspose_mul_self M).trace_nonneg

theorem normalizedTrace_isFaithful : IsFaithful (matrixProbabilitySpace ℂ n) := by
  intro M hM
  have ht : Matrix.trace (Mᴴ * M) = 0 := by
    change (Fintype.card n : ℂ)⁻¹ * Matrix.trace (Mᴴ * M) = 0 at hM
    exact (mul_eq_zero.mp hM).resolve_left (inv_ne_zero (dimension_ne_zero ℂ n))
  exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp ht

/-- Complex normalized matrix trace is positive and star-compatible. -/
noncomputable def matrixStarProbabilitySpace : StarProbabilitySpace (Matrix n n ℂ) where
  toProbabilitySpace := matrixProbabilitySpace ℂ n
  map_star := normalizedTrace_conjTranspose
  positive := normalizedTrace_star_mul_self_nonneg n

end FreeProbability

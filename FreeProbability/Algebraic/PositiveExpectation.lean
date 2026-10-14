import FreeProbability.Algebraic.StarProbabilitySpace
import Mathlib.Algebra.Order.Module.PositiveLinearMap

/-! # Positive expectations and order-compatible linear functionals -/

namespace FreeProbability.StarProbabilitySpace

open scoped ComplexOrder

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [PartialOrder A] [StarOrderedRing A]
    (φ : FreeProbability.StarProbabilitySpace A)

/-- Positivity on star squares extends to the entire canonical positive cone. -/
theorem expectation_nonneg {a : A} (ha : 0 ≤ a) : 0 ≤ φ.expectation a := by
  have h := StarOrderedRing.nonneg_iff.mp ha
  refine AddSubmonoid.closure_induction (motive := fun x _ => 0 ≤ φ.expectation x) ?_ ?_ ?_ h
  · intro x hx
    obtain ⟨y, rfl⟩ := hx
    exact φ.positive y
  · simp
  · intro a b _ _ ha hb
    rw [map_add]
    exact add_nonneg ha hb

/-- The existing algebraic expectation becomes a positive linear map. -/
def toPositiveLinearMap : A →ₚ[ℂ] ℂ where
  toLinearMap := φ.expectation
  monotone' := by
    intro a b hab
    have h := φ.expectation_nonneg (sub_nonneg.mpr hab)
    rw [map_sub] at h
    exact sub_nonneg.mp h

@[simp] theorem toPositiveLinearMap_apply (a : A) : φ.toPositiveLinearMap a = φ.expectation a := rfl

end FreeProbability.StarProbabilitySpace

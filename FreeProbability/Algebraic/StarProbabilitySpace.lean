import FreeProbability.Algebraic.ProbabilitySpace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

/-!
# Positive star probability spaces

An algebraic complex star probability space has a normalized, star-compatible,
positive expectation. Topology, C-star norm, and completeness are additional
requirements for an analytic probability space; they are not asserted here.
-/

namespace FreeProbability

open scoped ComplexOrder

variable (A : Type*) [Ring A] [Algebra ℂ A] [StarRing A]

/-- A positive normalized expectation on a complex star algebra. -/
structure StarProbabilitySpace extends ProbabilitySpace ℂ A where
  map_star : ∀ a, expectation (star a) = star (expectation a)
  positive : ∀ a, 0 ≤ expectation (star a * a)

variable {A}

/-- Faithfulness is stated separately so nonfaithful states remain usable. -/
def IsFaithful (φ : ProbabilitySpace ℂ A) : Prop :=
  ∀ a, φ.expectation (star a * a) = 0 → a = 0

namespace StarProbabilitySpace

variable (φ : StarProbabilitySpace A)

theorem expectation_star_mul_self_re_nonneg (a : A) :
    0 ≤ (φ.expectation (star a * a)).re := (φ.positive a).1

theorem expectation_star_mul_self_im_eq_zero (a : A) :
    (φ.expectation (star a * a)).im = 0 := (φ.positive a).2.symm

theorem expectation_selfAdjoint_im_eq_zero {a : A} (ha : star a = a) :
    (φ.expectation a).im = 0 := by
  have h := φ.map_star a
  rw [ha] at h
  have hi := congrArg Complex.im h
  simp only [Complex.star_def, Complex.conj_im] at hi
  linarith

end StarProbabilitySpace
end FreeProbability

import FreeProbability.Algebraic.PositiveExpectation
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal

/-! # Norm-one continuous expectations on unital C-star algebras

Continuity follows from positivity. The algebraic expectation is preserved;
traciality and faithfulness remain separate properties.
-/

namespace FreeProbability.StarProbabilitySpace

open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (φ : FreeProbability.StarProbabilitySpace A)

theorem expectation_star_mul_norm_sq_le (a b : A) :
    ‖φ.expectation (star a * b)‖ ^ 2 ≤
      ‖φ.expectation (star a * a)‖ * ‖φ.expectation (star b * b)‖ :=
  PositiveLinearMap.norm_map_star_mul_sq_le φ.toPositiveLinearMap a b

noncomputable def positiveContinuousExpectation : A →P[ℂ] ℂ :=
  PositiveContinuousLinearMap.ofClass φ.toPositiveLinearMap

noncomputable def continuousExpectation : A →L[ℂ] ℂ :=
  φ.positiveContinuousExpectation.toContinuousLinearMap

@[simp] theorem positiveContinuousExpectation_apply (a : A) :
    φ.positiveContinuousExpectation a = φ.expectation a := rfl

@[simp] theorem continuousExpectation_apply (a : A) :
    φ.continuousExpectation a = φ.expectation a := rfl

theorem continuousExpectation_norm : ‖φ.continuousExpectation‖ = 1 := by
  have h := PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one φ.positiveContinuousExpectation
  have hr := congrArg Complex.re h
  simpa only [continuousExpectation, Complex.ofReal_re, positiveContinuousExpectation_apply,
    φ.map_one, Complex.one_re] using hr

theorem expectation_norm_le (a : A) : ‖φ.expectation a‖ ≤ ‖a‖ := by
  have h := φ.continuousExpectation.le_opNorm a
  simpa only [continuousExpectation_apply, continuousExpectation_norm, one_mul] using h

theorem expectation_pow_norm_le (a : A) (k : ℕ) : ‖φ.expectation (a ^ k)‖ ≤ ‖a‖ ^ k := by
  let _ : Nontrivial A := φ.toProbabilitySpace.nontrivial
  exact (φ.expectation_norm_le (a ^ k)).trans (norm_pow_le a k)

theorem expectation_norm_sq_le (a : A) :
    ‖φ.expectation a‖ ^ 2 ≤ ‖φ.expectation (star a * a)‖ := by
  simpa only [star_one, one_mul, φ.map_one, norm_one] using
    φ.expectation_star_mul_norm_sq_le 1 a

theorem expectation_star_mul_re_le (a b : A) :
    ‖φ.expectation (star a * b)‖ ^ 2 ≤
      (φ.expectation (star a * a)).re * (φ.expectation (star b * b)).re := by
  have ha : ‖φ.expectation (star a * a)‖ = (φ.expectation (star a * a)).re := by
    simpa only [Complex.ofReal_re] using
      congrArg Complex.re (Complex.eq_coe_norm_of_nonneg (φ.positive a)).symm
  have hb : ‖φ.expectation (star b * b)‖ = (φ.expectation (star b * b)).re := by
    simpa only [Complex.ofReal_re] using
      congrArg Complex.re (Complex.eq_coe_norm_of_nonneg (φ.positive b)).symm
  simpa only [ha, hb] using φ.expectation_star_mul_norm_sq_le a b

theorem continuous_expectation : Continuous φ.expectation := φ.continuousExpectation.continuous

end FreeProbability.StarProbabilitySpace

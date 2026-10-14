import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Actual Duhamel commutators in real Banach algebras

The exponential is the genuine norm-convergent Banach-algebra exponential.
Differentiating its real scalar rays and applying the fundamental theorem of
calculus proves the ordered integral identity without assuming commutativity.
-/

noncomputable section
open scoped Interval
open NormedSpace

namespace FreeProbability

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- The ordered Duhamel integrand for the commutator with an actual exponential. -/
def exponentialCommutatorIntegrand (C X : A) (u : ℝ) : A :=
  exp ((1 - u) • X) * (C * X - X * C) * exp (u • X)

/-- The entire Duhamel integrand is norm-continuous. -/
theorem continuous_exponentialCommutatorIntegrand (C X : A) :
    Continuous (exponentialCommutatorIntegrand C X) := by
  have hc := (differentiable_exp_smul_const ℝ X).continuous
  exact ((hc.comp (continuous_const.sub continuous_id)).mul continuous_const).mul hc

/-- The derivative of the ordered exponential conjugation retains noncommutative order. -/
theorem hasDerivAt_exponentialConjugation (C X : A) (u : ℝ) :
    HasDerivAt (fun v : ℝ => exp ((1 - v) • X) * C * exp (v • X))
      (exponentialCommutatorIntegrand C X u) u := by
  have hL := (hasDerivAt_exp_smul_const X (1 - u)).scomp u
    ((hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_id u))
  have hR := hasDerivAt_exp_smul_const' X u
  convert (hL.mul_const C).mul hR using 1
  · rfl
  · simp only [Function.comp_apply, zero_sub, neg_smul, one_smul]
    unfold exponentialCommutatorIntegrand
    noncomm_ring

/-- Exact Duhamel commutator identity for every pair of elements of a real Banach algebra. -/
theorem exponential_commutator_eq_integral (C X : A) :
    C * exp X - exp X * C = ∫ u in (0 : ℝ)..1,
      exp ((1 - u) • X) * (C * X - X * C) * exp (u • X) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hasDerivAt_exponentialConjugation C X u)
    ((continuous_exponentialCommutatorIntegrand C X).intervalIntegrable 0 1)
  simpa only [exponentialCommutatorIntegrand, sub_self, zero_smul, exp_zero,
    one_mul, sub_zero, one_smul, mul_one] using h.symm

end FreeProbability

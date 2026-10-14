import FreeProbability.Fock.OrnsteinUhlenbeckNumberResolventInverse
import Mathlib.Analysis.InnerProductSpace.Positive

/-! Genuine Hilbert self-adjointness and full operator-cone positivity of the bounded number resolvent. -/
noncomputable section
open scoped Classical InnerProductSpace ComplexOrder
namespace FreeProbability.Fock
variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

 theorem numberResolvent_inner_symmetric (f g : TensorFullFock H) :
    inner ℂ (numberResolvent H f) g = inner ℂ f (numberResolvent H g) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  have hw : starRingEnd ℂ (numberResolventWeight n) = numberResolventWeight n := by
    unfold numberResolventWeight
    exact Complex.conj_ofReal _
  rw [numberResolvent_degree, numberResolvent_degree, inner_smul_left, inner_smul_right, hw]

/-- Actual Hilbert adjoint, on every completed vector, equals the bounded resolvent itself. -/
@[simp] theorem numberResolvent_adjoint : (numberResolvent H).adjoint = numberResolvent H := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  exact numberResolvent_inner_symmetric H

 theorem numberResolvent_quadratic_nonneg (f : TensorFullFock H) :
    0 ≤ inner ℂ f (numberResolvent H f) := by
  rw [lp.inner_eq_tsum]
  apply tsum_nonneg
  intro n
  rw [numberResolvent_degree, inner_smul_right, inner_self_eq_norm_sq_to_K]
  change 0 ≤ numberResolventWeight n * (‖f n‖ : ℂ) ^ 2
  apply Complex.nonneg_iff.mpr
  constructor
  · simp only [numberResolventWeight, Complex.mul_re, ← Complex.ofReal_pow,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    positivity
  · simp only [numberResolventWeight, Complex.mul_im, ← Complex.ofReal_pow,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, add_zero]

/-- Positivity in the genuine full cone of bounded Hilbert operators. -/
theorem numberResolvent_nonneg : 0 ≤ numberResolvent H := by
  apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
  apply (ContinuousLinearMap.isPositive_iff _).mpr
  constructor
  · exact numberResolvent_inner_symmetric H
  · intro f
    rw [numberResolvent_inner_symmetric]
    exact numberResolvent_quadratic_nonneg H f

end FreeProbability.Fock

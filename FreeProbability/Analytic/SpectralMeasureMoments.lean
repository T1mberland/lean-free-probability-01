import FreeProbability.Analytic.SpectralMeasureCalculus

/-! # Compatibility of actual spectral laws with power moments and algebraic polynomial laws -/

noncomputable section
open MeasureTheory

namespace FreeProbability

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (φ : StarProbabilitySpace A) {a : A} (ha : IsSelfAdjoint a)

/-- Actual scalar spectral power moments agree with the original algebraic moments. -/
theorem spectralMeasure_power_moment (n : ℕ) :
    φ.expectation (a ^ n) = (∫ x : ℝ, x ^ n ∂spectralMeasure φ ha : ℝ) := by
  have hi := expectation_cfc_eq_integral_on_spectrum φ ha (fun x : ℝ => x ^ n)
    (continuous_id.pow n).continuousOn
  rwa [cfc_pow_id a n ha] at hi

/-- Every power is genuinely integrable, because the original operator is bounded. -/
theorem spectralMeasure_integrable_pow (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (spectralMeasure φ ha) :=
  integrable_spectralMeasure φ ha _ (continuous_id.pow n).continuousOn

/-- All real polynomial laws agree with actual continuous functional calculus and the measure. -/
theorem spectralMeasure_real_polynomial (p : Polynomial ℝ) :
    φ.expectation (Polynomial.aeval a p) = (∫ x : ℝ, p.eval x ∂spectralMeasure φ ha : ℝ) := by
  have hi := expectation_cfc_eq_integral_on_spectrum φ ha p.eval p.continuous.continuousOn
  rwa [cfc_polynomial p a ha] at hi

/-- All complex algebraic polynomial laws are represented by the actual real spectral measure. -/
theorem spectralMeasure_complex_polynomial (p : Polynomial ℂ) :
    φ.expectation (Polynomial.aeval a p) = ∫ x : ℝ, p.eval (x : ℂ) ∂spectralMeasure φ ha := by
  have hi := expectation_complex_cfc_eq_integral φ ha p.eval p.continuous.continuousOn
  rwa [cfc_polynomial p a ha.isStarNormal] at hi

end FreeProbability

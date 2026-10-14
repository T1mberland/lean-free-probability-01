import FreeProbability.Analytic.SpectralMeasureSupport
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Continuous functional-calculus representation on the actual spectrum -/

noncomputable section
open scoped ComplexOrder
open MeasureTheory

namespace FreeProbability

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (φ : StarProbabilitySpace A) {a : A} (ha : IsSelfAdjoint a)

/-- The constructed probability measure equals its restriction to the actual spectrum. -/
theorem spectralMeasure_restrict_spectrum :
    (spectralMeasure φ ha).restrict (spectrum ℝ a) = spectralMeasure φ ha :=
  Measure.restrict_eq_self_of_ae_mem (spectralMeasure_spectrum_compl φ ha)

/-- Continuity on the actual spectrum suffices for measurability under the spectral law. -/
theorem aestronglyMeasurable_spectralMeasure {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E) (hf : ContinuousOn f (spectrum ℝ a)) :
    AEStronglyMeasurable f (spectralMeasure φ ha) := by
  have hm := hf.aestronglyMeasurable (ContinuousFunctionalCalculus.isCompact_spectrum a).measurableSet
    (μ := spectralMeasure φ ha)
  rwa [spectralMeasure_restrict_spectrum] at hm

/-- Every continuous spectral function is integrable against the actual probability law. -/
theorem integrable_spectralMeasure {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E) (hf : ContinuousOn f (spectrum ℝ a)) : Integrable f (spectralMeasure φ ha) := by
  have hi := hf.integrableOn_compact (ContinuousFunctionalCalculus.isCompact_spectrum a)
    (μ := spectralMeasure φ ha)
  change Integrable f ((spectralMeasure φ ha).restrict (spectrum ℝ a)) at hi
  rwa [spectralMeasure_restrict_spectrum] at hi

/-- The real CFC representation only needs continuity on the actual spectrum. -/
theorem expectation_cfc_eq_integral_on_spectrum (f : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ a)) :
    φ.expectation (cfc f a) = (∫ x, f x ∂spectralMeasure φ ha : ℝ) := by
  have hi : (∫ x, f x ∂spectralMeasure φ ha) = (φ.expectation (cfc f a)).re := by
    rw [spectralMeasure, integral_map continuous_subtype_val.measurable.aemeasurable
      (aestronglyMeasurable_spectralMeasure φ ha f hf), cfc_apply f a ha hf]
    exact integral_spectralMeasureOnSpectrum φ ha ⟨_, hf.domRestrict⟩
  apply Complex.ext
  · exact hi.symm
  · simp only [Complex.ofReal_im]
    exact φ.expectation_selfAdjoint_im_eq_zero (cfc_predicate f a)

omit [PartialOrder A] [StarOrderedRing A] in
/-- Real and imaginary parts give the actual complex CFC decomposition for self-adjoint input. -/
theorem cfc_complex_re_im (ha : IsSelfAdjoint a) (f : ℂ → ℂ) (hf : ContinuousOn f (spectrum ℂ a)) :
    cfc f a = cfc (fun x : ℝ => (f x).re) a +
      Complex.I • cfc (fun x : ℝ => (f x).im) a := by
  have hr : ContinuousOn (fun x => ((f x).re : ℂ)) (spectrum ℂ a) :=
    Complex.continuous_ofReal.comp_continuousOn (Complex.continuous_re.comp_continuousOn hf)
  have hi : ContinuousOn (fun x => ((f x).im : ℂ)) (spectrum ℂ a) :=
    Complex.continuous_ofReal.comp_continuousOn (Complex.continuous_im.comp_continuousOn hf)
  have he : f = fun x => ((f x).re : ℂ) + Complex.I • ((f x).im : ℂ) := by
    funext x
    simpa only [smul_eq_mul, mul_comm] using (Complex.re_add_im (f x)).symm
  calc
    cfc f a = cfc (fun x => ((f x).re : ℂ) + Complex.I • ((f x).im : ℂ)) a := congrArg (fun g => cfc g a) he
    _ = cfc (fun x => ((f x).re : ℂ)) a + Complex.I • cfc (fun x => ((f x).im : ℂ)) a := by
      have hadd := cfc_add a (fun x => ((f x).re : ℂ))
        (fun x => Complex.I • ((f x).im : ℂ)) hr (hi.const_smul Complex.I)
      exact hadd.trans (congrArg (fun t => cfc (fun x => ((f x).re : ℂ)) a + t)
        (cfc_smul Complex.I (fun x => ((f x).im : ℂ)) a hi))
    _ = _ := by
      rw [cfc_complex_eq_real a (fun _ _ => by simp) ha,
        cfc_complex_eq_real a (fun _ _ => by simp) ha]
      simp only [Complex.ofReal_re]

/-- Complex-valued continuous functional calculus has its actual spectral probability integral law. -/
theorem expectation_complex_cfc_eq_integral (f : ℂ → ℂ)
    (hf : ContinuousOn f (spectrum ℂ a)) :
    φ.expectation (cfc f a) = ∫ x : ℝ, f x ∂spectralMeasure φ ha := by
  have hreal : ContinuousOn (fun x : ℝ => f x) (spectrum ℝ a) := by
    apply hf.comp Complex.continuous_ofReal.continuousOn
    intro x hx
    exact spectrum.algebraMap_mem ℂ hx
  have hr : ContinuousOn (fun x : ℝ => (f x).re) (spectrum ℝ a) :=
    Complex.continuous_re.comp_continuousOn hreal
  have hi : ContinuousOn (fun x : ℝ => (f x).im) (spectrum ℝ a) :=
    Complex.continuous_im.comp_continuousOn hreal
  rw [cfc_complex_re_im ha f hf, map_add, map_smul,
    expectation_cfc_eq_integral_on_spectrum φ ha _ hr,
    expectation_cfc_eq_integral_on_spectrum φ ha _ hi]
  have hint := integral_re_add_im (integrable_spectralMeasure φ ha _ hreal)
  simp only [RCLike.re_to_complex, RCLike.im_to_complex, RCLike.I_to_complex] at hint
  convert hint using 1
  apply Complex.ext <;> simp [smul_eq_mul, mul_comm]

end FreeProbability

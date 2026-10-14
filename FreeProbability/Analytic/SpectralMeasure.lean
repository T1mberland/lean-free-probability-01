import FreeProbability.Analytic.SpectralMeasureFunctional

/-!
# Actual spectral probability measures

Riesz representation produces a genuine probability measure on the compact real
spectrum of a self-adjoint element. Its inclusion pushforward is a real measure
concentrated on that spectrum. Faithful support identification is separate.
-/

noncomputable section
open scoped ComplexOrder CompactlySupported
open MeasureTheory

namespace FreeProbability

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (φ : StarProbabilitySpace A) {a : A} (ha : IsSelfAdjoint a)

/-- The actual Riesz representing measure on the compact real spectrum. -/
def spectralMeasureOnSpectrum : Measure (spectrum ℝ a) :=
  RealRMK.rieszMeasure (spectralRieszFunctional φ ha)

instance : IsFiniteMeasure (spectralMeasureOnSpectrum φ ha) := by
  unfold spectralMeasureOnSpectrum
  infer_instance

/-- The Riesz measure represents the original real continuous-functional-calculus state. -/
theorem integral_spectralMeasureOnSpectrum (f : C(spectrum ℝ a, ℝ)) :
    ∫ x, f x ∂spectralMeasureOnSpectrum φ ha = (φ.expectation (cfcHom ha f)).re := by
  exact RealRMK.integral_rieszMeasure (spectralRieszFunctional φ ha)
    (CompactlySupportedContinuousMap.continuousMapEquiv f)

instance : IsProbabilityMeasure (spectralMeasureOnSpectrum φ ha) := by
  apply isProbabilityMeasure_iff_real.mpr
  have hi := integral_spectralMeasureOnSpectrum φ ha (1 : C(spectrum ℝ a, ℝ))
  simpa only [ContinuousMap.one_apply, integral_const, smul_eq_mul, mul_one,
    map_one, φ.map_one, Complex.one_re] using hi

/-- The spectral probability measure on the real line, obtained by the actual inclusion pushforward. -/
def spectralMeasure : Measure ℝ := (spectralMeasureOnSpectrum φ ha).map Subtype.val

instance : IsProbabilityMeasure (spectralMeasure φ ha) := by
  unfold spectralMeasure
  infer_instance

/-- The spectral measure is concentrated on the actual compact spectrum. -/
theorem spectralMeasure_spectrum_compl : spectralMeasure φ ha (spectrum ℝ a)ᶜ = 0 := by
  rw [spectralMeasure, Measure.map_apply continuous_subtype_val.measurable
    (ContinuousFunctionalCalculus.isCompact_spectrum a).measurableSet.compl]
  have he : (Subtype.val ⁻¹' (spectrum ℝ a)ᶜ : Set (spectrum ℝ a)) = ∅ := by
    ext x
    simp
  rw [he, measure_empty]

/-- Real continuous functional calculus has the actual integral representation on the real line. -/
theorem integral_spectralMeasure_cfc (f : ℝ → ℝ) (hf : Continuous f) :
    ∫ x, f x ∂spectralMeasure φ ha = (φ.expectation (cfc f a)).re := by
  rw [spectralMeasure, integral_map continuous_subtype_val.measurable.aemeasurable hf.aestronglyMeasurable,
    cfc_apply f a ha hf.continuousOn]
  exact integral_spectralMeasureOnSpectrum φ ha ⟨_, hf.continuousOn.domRestrict⟩

/-- The full complex-valued expectation of real functional calculus equals the real integral. -/
theorem expectation_cfc_eq_integral (f : ℝ → ℝ) (hf : Continuous f) :
    φ.expectation (cfc f a) = (∫ x, f x ∂spectralMeasure φ ha : ℝ) := by
  apply Complex.ext
  · exact (integral_spectralMeasure_cfc φ ha f hf).symm
  · simp only [Complex.ofReal_im]
    exact φ.expectation_selfAdjoint_im_eq_zero (cfc_predicate f a)

end FreeProbability

import FreeProbability.Semicircular.SpectralFock
import FreeProbability.Semicircular.SpectralDensitySupport
import FreeProbability.Analytic.SpectralMeasureCompactMoments

/-! # Identification of the actual Fock spectral probability measure with the explicit semicircle density -/

noncomputable section
open scoped Classical
open MeasureTheory Set

namespace FreeProbability.Fock

variable {I : Type*}

/-- The genuine Fock spectral law is exactly Lebesgue measure with the explicit semicircle density. -/
theorem fockSpectralLaw_eq_semicircleMeasure (i : I) :
    fockSpectralLaw i = Semicircular.semicircleMeasure := by
  have hmass : fockSpectralLaw i (Icc (-2 : ℝ) 2)ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.mpr (fockSpectralLaw_support_subset i)) Measure.measure_compl_support
  apply probabilityMeasure_eq_of_compact_power_moments (fockSpectralLaw i) Semicircular.semicircleMeasure
    isCompact_Icc hmass Semicircular.semicircleMeasure_Icc_compl
  intro n
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [show n = 2 * k by omega, fockSpectralLaw_even_moment, Semicircular.semicircleMeasure_even_moment]
  · rw [show n = 2 * k + 1 by omega, fockSpectralLaw_odd_moment, Semicircular.semicircleMeasure_odd_moment]

/-- The actual faithful Fock semicircular spectral law has full support `[-2,2]`. -/
theorem fockSpectralLaw_support (i : I) : (fockSpectralLaw i).support = Icc (-2 : ℝ) 2 := by
  rw [fockSpectralLaw_eq_semicircleMeasure, Semicircular.semicircleMeasure_support]

/-- The actual generated-algebra semicircular element has exactly the norm-two interval as spectrum. -/
theorem spectrum_closedSemicircular_real (i : I) : spectrum ℝ (closedSemicircular i) = Icc (-2 : ℝ) 2 := by
  rw [← fockSpectralLaw_support_eq_spectrum, fockSpectralLaw_support]

/-- Spectral permanence gives the exact spectrum of the original bounded Fock operator itself. -/
theorem spectrum_semicircular_real (i : I) : spectrum ℝ (semicircular i) = Icc (-2 : ℝ) 2 := by
  have hp : spectrum ℝ (closedSemicircular i) = spectrum ℝ (semicircular i) := by
    ext x
    rw [← spectrum.algebraMap_mem_iff ℂ, ← spectrum.algebraMap_mem_iff ℂ]
    exact StarSubalgebra.mem_spectrum_iff (closedSemicircularAlgebra I)
  rw [← hp, spectrum_closedSemicircular_real]

end FreeProbability.Fock

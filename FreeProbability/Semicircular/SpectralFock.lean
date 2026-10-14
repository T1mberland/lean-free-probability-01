import FreeProbability.Analytic.SpectralMeasureUniqueness
import FreeProbability.Fock.CatalanMoments

/-!
# Actual compact spectral laws of the genuine Fock semicircular generators

This constructs the actual probability measure and proves its Catalan moments
and compact support. Its identification with an explicit semicircle density is
a separate weighted-integral theorem, not assumed from the name of the family.
-/

noncomputable section
open scoped Classical
open MeasureTheory

namespace FreeProbability.Fock

variable {I : Type*}

local instance : PartialOrder (closedSemicircularAlgebra I) := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing (closedSemicircularAlgebra I) := CStarAlgebra.spectralOrderedRing _

/-- The actual spectral probability measure of a genuine canonical Fock generator. -/
def fockSpectralLaw (i : I) : Measure ℝ :=
  spectralMeasure (closedGeneratedVacuumState I) (isSelfAdjoint_closedSemicircular i)

instance (i : I) : IsProbabilityMeasure (fockSpectralLaw i) := by
  unfold fockSpectralLaw
  infer_instance

/-- Actual even spectral moments, rather than only algebraic moments, are Catalan numbers. -/
theorem fockSpectralLaw_even_moment (i : I) (n : ℕ) :
    ∫ x : ℝ, x ^ (2 * n) ∂fockSpectralLaw i = (catalan n : ℝ) := by
  have he := spectralMeasure_power_moment (closedGeneratedVacuumState I)
    (isSelfAdjoint_closedSemicircular i) (2 * n)
  rw [closedGeneratedVacuumState_even] at he
  simpa only [fockSpectralLaw, Complex.ofReal_re, Complex.natCast_re] using congrArg Complex.re he.symm

/-- Actual odd spectral moments vanish. -/
theorem fockSpectralLaw_odd_moment (i : I) (n : ℕ) :
    ∫ x : ℝ, x ^ (2 * n + 1) ∂fockSpectralLaw i = 0 := by
  have he := spectralMeasure_power_moment (closedGeneratedVacuumState I)
    (isSelfAdjoint_closedSemicircular i) (2 * n + 1)
  rw [closedGeneratedVacuumState_odd] at he
  simpa only [fockSpectralLaw, Complex.ofReal_re, Complex.zero_re] using congrArg Complex.re he.symm

/-- Faithfulness identifies the support with the spectrum of the actual generated-algebra element. -/
theorem fockSpectralLaw_support_eq_spectrum (i : I) :
    (fockSpectralLaw i).support = spectrum ℝ (closedSemicircular i) :=
  spectralMeasure_support_eq_spectrum (closedGeneratedVacuumState I)
    (isSelfAdjoint_closedSemicircular i) (closedGeneratedVacuumState_isFaithful I)

/-- The actual spectral law is compactly supported within the norm-two interval. -/
theorem fockSpectralLaw_support_subset (i : I) :
    (fockSpectralLaw i).support ⊆ Set.Icc (-2 : ℝ) 2 := by
  rw [fockSpectralLaw_support_eq_spectrum]
  let _ : Nontrivial (closedSemicircularAlgebra I) := (closedGeneratedVacuumState I).toProbabilitySpace.nontrivial
  intro x hx
  have hn := spectrum.norm_le_norm_of_mem hx
  rw [norm_closedSemicircular, Real.norm_eq_abs] at hn
  exact abs_le.mp hn

/-- The actual spectral law is independent of the chosen canonical orthonormal index and ambient size. -/
theorem fockSpectralLaw_eq {J : Type*} (i : I) (j : J) : fockSpectralLaw i = fockSpectralLaw j := by
  apply spectralMeasure_eq_of_power_moments (closedGeneratedVacuumState I) (closedGeneratedVacuumState J)
    (isSelfAdjoint_closedSemicircular i) (isSelfAdjoint_closedSemicircular j)
  intro n
  change vacuumExpectation ((closedSemicircularAlgebra I).val (closedSemicircular i ^ n)) =
    vacuumExpectation ((closedSemicircularAlgebra J).val (closedSemicircular j ^ n))
  rw [map_pow, map_pow]
  change vacuumExpectation (semicircular i ^ n) = vacuumExpectation (semicircular j ^ n)
  rw [vacuumExpectation_semicircular_pow, vacuumExpectation_semicircular_pow]

end FreeProbability.Fock

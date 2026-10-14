import FreeProbability.Fock.OrthonormalFamilyCalculus
import FreeProbability.Semicircular.SpectralIdentification
import FreeProbability.Analytic.SpectralMeasureCauchy

/-!
# The actual semicircle spectral distribution of arbitrary orthonormal families

The spectral measure is constructed from the actual faithful vacuum state on
the literal family-generated C-star algebra. Moment uniqueness identifies it
with the explicit normalized square-root Lebesgue density. Faithfulness and
spectral permanence then give the exact spectrum of the original Fock fields.
-/

noncomputable section
open scoped Classical
open MeasureTheory Set

namespace FreeProbability.Fock.OrthonormalFamilyExtension

variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {e : I → H} (d : OrthonormalFamilyExtension e)

local instance : PartialOrder d.generatedAlgebra := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing d.generatedAlgebra := CStarAlgebra.spectralOrderedRing _
local instance : PartialOrder (closedSemicircularAlgebra d.indices) := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing (closedSemicircularAlgebra d.indices) := CStarAlgebra.spectralOrderedRing _

/-- The actual spectral probability measure of a prescribed orthonormal-family generator. -/
def spectralLaw (i : I) : Measure ℝ := spectralMeasure d.state (d.isSelfAdjoint_generator i)

instance (i : I) : IsProbabilityMeasure (d.spectralLaw i) := by
  unfold spectralLaw
  infer_instance

/-- The actual family-generated state and the full extension give the same spectral law. -/
theorem spectralLaw_eq_canonical (i : I) : d.spectralLaw i = fockSpectralLaw (d.index i) := by
  apply spectralMeasure_eq_of_power_moments d.state (closedGeneratedVacuumState d.indices)
    (d.isSelfAdjoint_generator i) (isSelfAdjoint_closedSemicircular (d.index i))
  intro n
  change vacuumExpectation (d.generatedAlgebra.val (d.generator i ^ n)) =
    vacuumExpectation ((closedSemicircularAlgebra d.indices).val (closedSemicircular (d.index i) ^ n))
  rw [map_pow, map_pow]
  change vacuumExpectation (d.field i ^ n) = vacuumExpectation (semicircular (d.index i) ^ n)
  rw [d.field_eq_semicircular]

/-- The actual spectral distribution is the explicit square-root semicircle density on `[-2,2]`. -/
theorem spectralLaw_eq_semicircleMeasure (i : I) :
    d.spectralLaw i = Semicircular.semicircleMeasure := by
  rw [d.spectralLaw_eq_canonical, fockSpectralLaw_eq_semicircleMeasure]

/-- The actual spectral distribution has full support on the entire norm-two interval. -/
theorem spectralLaw_support (i : I) : (d.spectralLaw i).support = Icc (-2 : ℝ) 2 := by
  rw [d.spectralLaw_eq_semicircleMeasure, Semicircular.semicircleMeasure_support]

/-- Each generator's exact spectrum in its own literal generated C-star algebra. -/
theorem spectrum_generator (i : I) : spectrum ℝ (d.generator i) = Icc (-2 : ℝ) 2 := by
  rw [← spectralMeasure_support_eq_spectrum d.state (d.isSelfAdjoint_generator i) d.state_isFaithful]
  exact d.spectralLaw_support i

/-- Each original bounded adapted Fock field itself has exactly the semicircular spectrum. -/
theorem spectrum_field (i : I) : spectrum ℝ (d.field i) = Icc (-2 : ℝ) 2 := by
  rw [d.field_eq_semicircular]
  exact spectrum_semicircular_real _

/-- Continuous complex functional calculus integrates against the explicit semicircle law.
Only continuity on the actual spectrum is required. -/
theorem expectation_complex_cfc (i : I) (f : ℂ → ℂ)
    (hf : ContinuousOn f (spectrum ℂ (d.generator i))) :
    d.state.expectation (cfc f (d.generator i)) =
      ∫ x : ℝ, f x ∂Semicircular.semicircleMeasure := by
  have h := expectation_complex_cfc_eq_integral d.state (d.isSelfAdjoint_generator i) f hf
  change d.state.expectation (cfc f (d.generator i)) =
    ∫ x : ℝ, f x ∂d.spectralLaw i at h
  rwa [d.spectralLaw_eq_semicircleMeasure] at h

/-- The actual resolvent Cauchy transform has the explicit semicircle integral on its entire domain. -/
theorem cauchyTransform_semicircle (i : I) (z : ℂ)
    (hz : z ∈ resolventSet ℂ (d.generator i)) :
    d.state.cauchyTransform (d.generator i) z =
      ∫ x : ℝ, (z - (x : ℂ))⁻¹ ∂Semicircular.semicircleMeasure := by
  have h := cauchyTransform_eq_spectralIntegral d.state (d.isSelfAdjoint_generator i) z hz
  change d.state.cauchyTransform (d.generator i) z =
    ∫ x : ℝ, (z - (x : ℂ))⁻¹ ∂d.spectralLaw i at h
  rwa [d.spectralLaw_eq_semicircleMeasure] at h

end FreeProbability.Fock.OrthonormalFamilyExtension

namespace FreeProbability.Fock

/-- Every orthonormal family in a complete complex Hilbert space admits the genuine
adapted full Fock realization with a faithful tracial free semicircular system.
The basis extension supplies complete tensor levels without a spanning hypothesis. -/
theorem exists_fullFock_semicircular_family {I H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {e : I → H} (he : Orthonormal ℂ e) :
    ∃ d : OrthonormalFamilyExtension e,
      IsFaithful d.state.toProbabilitySpace ∧ IsTracial d.state.toProbabilitySpace ∧
      FreelyIndependent d.state.toProbabilitySpace d.generatorAlgebra ∧
      ∀ i : I, IsSelfAdjoint (d.generator i) ∧ ‖d.generator i‖ = 2 ∧
        d.state.expectation (d.generator i) = 0 ∧
        d.state.expectation (d.generator i ^ 2) = 1 ∧
        d.spectralLaw i = Semicircular.semicircleMeasure ∧
        spectrum ℝ (d.generator i) = Icc (-2 : ℝ) 2 := by
  let d := orthonormalFamilyExtension he
  refine ⟨d, d.state_isFaithful, d.state_isTracial, d.freelyIndependent_state, ?_⟩
  intro i
  exact ⟨d.isSelfAdjoint_generator i, d.norm_generator i, d.centered i,
    d.variance_one i, d.spectralLaw_eq_semicircleMeasure i, d.spectrum_generator i⟩

end FreeProbability.Fock


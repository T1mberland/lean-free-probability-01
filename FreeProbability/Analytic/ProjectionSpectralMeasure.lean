import FreeProbability.Analytic.SpectralMeasureMoments
import FreeProbability.Analytic.ProjectionTransform
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-! # The actual two-atom spectral law of a projection -/

noncomputable section
open MeasureTheory Set
open scoped Classical
namespace FreeProbability

/-- Concentration on two distinct points gives an actual measure decomposition. -/
theorem measure_eq_two_dirac_of_concentration {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] (μ : Measure X) {a b : X} (hab : a ≠ b)
    (hμ : μ ({a, b} : Set X)ᶜ = 0) :
    μ = μ {a} • Measure.dirac a + μ {b} • Measure.dirac b := by
  have hr : μ.restrict ({a, b} : Set X) = μ :=
    Measure.restrict_eq_self_of_ae_mem (by simpa only [ae_iff, Set.compl_def] using hμ)
  calc
    μ = μ.restrict ({a, b} : Set X) := hr.symm
    _ = _ := by
      change μ.restrict ({a} ∪ {b}) = _
      rw [Measure.restrict_union (disjoint_singleton.mpr hab) (measurableSet_singleton b),
        Measure.restrict_singleton, Measure.restrict_singleton]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (φ : StarProbabilitySpace A) {p : A} (hp : IsSelfAdjoint p) (hpi : IsIdempotentElem p)

include hp hpi

/-- The actual projection law is concentrated on zero and one. -/
theorem spectralMeasure_projection_concentration :
    spectralMeasure φ hp ({0, 1} : Set ℝ)ᶜ = 0 :=
  measure_mono_null (compl_subset_compl.mpr (hpi.spectrum_subset ℝ))
    (spectralMeasure_spectrum_compl φ hp)

/-- Actual masses, without assuming a supplied Bernoulli law. -/
theorem spectralMeasure_projection_atoms :
    spectralMeasure φ hp = spectralMeasure φ hp {0} • Measure.dirac 0 +
      spectralMeasure φ hp {1} • Measure.dirac 1 :=
  measure_eq_two_dirac_of_concentration _ zero_ne_one
    (spectralMeasure_projection_concentration φ hp hpi)

/-- The weight of the atom at one is exactly the original state expectation. -/
theorem projection_expectation_eq_mass_one :
    φ.expectation p = ((spectralMeasure φ hp {1}).toReal : ℂ) := by
  let μ := spectralMeasure φ hp
  have hd : μ = μ {0} • Measure.dirac 0 + μ {1} • Measure.dirac 1 :=
    spectralMeasure_projection_atoms φ hp hpi
  have hi : Integrable (fun x : ℝ => x) μ := by
    simpa using spectralMeasure_integrable_pow φ hp 1
  have h0 : Integrable (fun x : ℝ => x) (μ {0} • Measure.dirac 0) :=
    hi.mono_measure ((Measure.le_iff'.mpr (fun s => by rw [Measure.add_apply]; exact le_add_right le_rfl)).trans_eq hd.symm)
  have h1 : Integrable (fun x : ℝ => x) (μ {1} • Measure.dirac 1) :=
    hi.mono_measure ((Measure.le_iff'.mpr (fun s => by rw [Measure.add_apply]; exact le_add_left le_rfl)).trans_eq hd.symm)
  have he : (∫ x : ℝ, x ∂μ) = (μ {1}).toReal := by
    calc
      _ = ∫ x : ℝ, x ∂(μ {0} • Measure.dirac 0 + μ {1} • Measure.dirac 1) :=
        congrArg (fun ν : Measure ℝ => ∫ x : ℝ, x ∂ν) hd
      _ = _ := by
        rw [integral_add_measure h0 h1]
        simp [integral_smul_measure]
  have hm := spectralMeasure_power_moment φ hp 1
  simp only [pow_one] at hm
  change φ.expectation p = (∫ x : ℝ, x ∂μ : ℝ) at hm
  rwa [he] at hm

/-- The two finite atom masses sum to one in real scalars. -/
theorem spectralMeasure_projection_real_mass_sum :
    (spectralMeasure φ hp {0}).toReal + (spectralMeasure φ hp {1}).toReal = 1 := by
  let μ := spectralMeasure φ hp
  have hsum : μ {0} + μ {1} = 1 := by
    rw [← measure_union (disjoint_singleton.mpr (zero_ne_one : (0 : ℝ) ≠ 1))
      (measurableSet_singleton 1)]
    exact (measure_of_measure_compl_eq_zero (spectralMeasure_projection_concentration φ hp hpi)).trans
      (measure_univ : μ univ = 1)
  have ht := congrArg ENNReal.toReal hsum
  simpa only [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _), ENNReal.toReal_one] using ht

/-- A projection's trace parameter belongs to the genuine probability interval. -/
theorem projection_expectation_re_mem_Icc : (φ.expectation p).re ∈ Icc (0 : ℝ) 1 := by
  rw [projection_expectation_eq_mass_one φ hp hpi, Complex.ofReal_re]
  have hs := spectralMeasure_projection_real_mass_sum φ hp hpi
  exact ⟨ENNReal.toReal_nonneg, by linarith [ENNReal.toReal_nonneg (a := spectralMeasure φ hp {0})]⟩

/-- The actual spectral law is `(1-α)δ₀ + αδ₁`, with α the original expectation. -/
theorem spectralMeasure_projection :
    spectralMeasure φ hp = ENNReal.ofReal (1 - (φ.expectation p).re) • Measure.dirac 0 +
      ENNReal.ofReal (φ.expectation p).re • Measure.dirac 1 := by
  rw [projection_expectation_eq_mass_one φ hp hpi, Complex.ofReal_re]
  have hs := spectralMeasure_projection_real_mass_sum φ hp hpi
  have h0 : 1 - (spectralMeasure φ hp {1}).toReal = (spectralMeasure φ hp {0}).toReal := by linarith
  rw [h0, ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact spectralMeasure_projection_atoms φ hp hpi

/-- The existing actual analytic S germ has the same real trace parameter as
this spectral law; the nonzero first moment is the precise inverse-germ domain. -/
theorem projection_sTransform_eventually (h : φ.expectation p ≠ 0) :
    ∀ᶠ w in nhds (0 : ℂ), φ.sTransform p h w =
      (1 + w) / (((φ.expectation p).re : ℂ) + w) := by
  have hr : ((φ.expectation p).re : ℂ) = φ.expectation p := by
    rw [projection_expectation_eq_mass_one φ hp hpi]
    simp only [Complex.ofReal_re]
  simpa only [hr] using φ.sTransform_idempotent_eventually p hpi h

end FreeProbability

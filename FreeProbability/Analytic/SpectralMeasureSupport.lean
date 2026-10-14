import FreeProbability.Analytic.SpectralMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.UrysohnsLemma

/-! # Spectral concentration and faithfulness of the representing functional -/

noncomputable section
open scoped ComplexOrder CompactlySupported Topology
open MeasureTheory

namespace FreeProbability

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (φ : StarProbabilitySpace A) {a : A} (ha : IsSelfAdjoint a)

/-- Even without faithfulness, the actual real spectral measure has compact spectral support. -/
theorem spectralMeasure_support_subset : (spectralMeasure φ ha).support ⊆ spectrum ℝ a := by
  apply Measure.support_subset_of_isClosed (ContinuousFunctionalCalculus.isCompact_spectrum a).isClosed
  exact spectralMeasure_spectrum_compl φ ha

/-- Full complex expectation of real compact-spectrum functional calculus. -/
theorem expectation_cfcHom_eq_integral (f : C(spectrum ℝ a, ℝ)) :
    φ.expectation (cfcHom ha f) = (∫ x, f x ∂spectralMeasureOnSpectrum φ ha : ℝ) := by
  apply Complex.ext
  · exact (integral_spectralMeasureOnSpectrum φ ha f).symm
  · simp only [Complex.ofReal_im]
    apply φ.expectation_selfAdjoint_im_eq_zero
    rw [← map_star]
    congr 1


/-- Faithfulness of the original state gives an exact square-integral kernel criterion. -/
theorem integral_square_eq_zero_iff (hfaith : IsFaithful φ.toProbabilitySpace)
    (f : C(spectrum ℝ a, ℝ)) :
    (∫ x, (f x) ^ 2 ∂spectralMeasureOnSpectrum φ ha) = 0 ↔ f = 0 := by
  constructor
  · intro hzero
    have he : φ.expectation (star (cfcHom ha f) * cfcHom ha f) = 0 := by
      rw [← map_star, ← map_mul, expectation_cfcHom_eq_integral]
      have hf : (fun x : spectrum ℝ a => (star f * f) x) = fun x => (f x) ^ 2 := by
        funext x
        simp [pow_two]
      rw [hf, hzero]
      rfl
    have hz := hfaith (cfcHom ha f) he
    apply cfcHom_injective ha
    simpa only [map_zero] using hz
  · intro hf
    subst f
    simp

/-- Every point of the actual spectrum has positive mass in each neighborhood under faithfulness. -/
theorem spectralMeasureOnSpectrum_support_eq_univ (hfaith : IsFaithful φ.toProbabilitySpace) :
    (spectralMeasureOnSpectrum φ ha).support = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  rw [Measure.mem_support_iff_forall]
  intro U hU
  by_contra hpos
  have hzero : spectralMeasureOnSpectrum φ ha U = 0 := le_antisymm (le_of_not_gt hpos) bot_le
  obtain ⟨V, hVU, hVopen, hxV⟩ := mem_nhds_iff.mp hU
  have hVzero : spectralMeasureOnSpectrum φ ha V = 0 :=
    le_antisymm ((measure_mono hVU).trans_eq hzero) bot_le
  obtain ⟨f, hf1, _, hfV, _⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen
    (isCompact_singleton (x := x)) hVopen (Set.singleton_subset_iff.mpr hxV)
  have hae : ∀ᵐ y ∂spectralMeasureOnSpectrum φ ha, y ∉ V := by
    rw [ae_iff]
    simpa using hVzero
  have hfzero : (∫ y, (f y) ^ 2 ∂spectralMeasureOnSpectrum φ ha) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hae] with y hy
    have hf : f y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (hfV h))
    simp [hf]
  have hfeq := (integral_square_eq_zero_iff φ ha hfaith f).mp hfzero
  have hone : f x = 1 := hf1 (Set.mem_singleton x)
  rw [hfeq] at hone
  simp at hone

/-- Faithfulness identifies the support of the actual real measure with the actual spectrum. -/
theorem spectralMeasure_support_eq_spectrum (hfaith : IsFaithful φ.toProbabilitySpace) :
    (spectralMeasure φ ha).support = spectrum ℝ a := by
  apply Set.Subset.antisymm (spectralMeasure_support_subset φ ha)
  intro x hx
  rw [Measure.mem_support_iff_forall]
  intro U hU
  obtain ⟨V, hVU, hVopen, hxV⟩ := mem_nhds_iff.mp hU
  let x' : spectrum ℝ a := ⟨x, hx⟩
  have hs : x' ∈ (spectralMeasureOnSpectrum φ ha).support := by
    rw [spectralMeasureOnSpectrum_support_eq_univ φ ha hfaith]
    trivial
  have hn : Subtype.val ⁻¹' V ∈ 𝓝 x' :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds (hVopen.mem_nhds hxV)
  have hp := (Measure.mem_support_iff_forall x').mp hs _ hn
  have hm : 0 < spectralMeasure φ ha V := by
    rw [spectralMeasure, Measure.map_apply continuous_subtype_val.measurable hVopen.measurableSet]
    exact hp
  exact hm.trans_le (measure_mono hVU)

end FreeProbability

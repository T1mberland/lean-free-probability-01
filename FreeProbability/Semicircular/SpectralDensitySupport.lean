import FreeProbability.Semicircular.SpectralDensityMeasure
import Mathlib.MeasureTheory.Measure.Support

/-! # The support of the explicit semicircle probability measure is exactly the norm-two interval -/

noncomputable section
open scoped Topology
open MeasureTheory Set

namespace FreeProbability.Semicircular

/-- The actual density is strictly positive throughout the open semicircle interval. -/
theorem semicircleDensity_pos {x : ℝ} (hx : x ∈ Ioo (-2 : ℝ) 2) : 0 < semicircleDensity x := by
  have hs : 0 < 4 - x ^ 2 := by
    have hp := mul_pos (show 0 < x + 2 by linarith [hx.1]) (show 0 < 2 - x by linarith [hx.2])
    nlinarith
  exact div_pos (Real.sqrt_pos.mpr hs) (mul_pos (by norm_num) Real.pi_pos)

/-- Every interior point belongs to the support of the actual density measure. -/
theorem Ioo_subset_semicircleMeasure_support : Ioo (-2 : ℝ) 2 ⊆ semicircleMeasure.support := by
  intro x hx
  rw [Measure.mem_support_iff_forall]
  intro U hU
  by_contra hpos
  have hzero : semicircleMeasure U = 0 := le_antisymm (le_of_not_gt hpos) bot_le
  have hm : Measurable (fun y => ENNReal.ofReal (semicircleDensity y)) :=
    ENNReal.measurable_ofReal.comp continuous_semicircleDensity.measurable
  have hz : volume ({y | ENNReal.ofReal (semicircleDensity y) ≠ 0} ∩ U) = 0 :=
    (withDensity_apply_eq_zero hm).mp hzero
  have hn : ENNReal.ofReal (semicircleDensity x) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (semicircleDensity_pos hx)).ne'
  have hopen : IsOpen {y | ENNReal.ofReal (semicircleDensity y) ≠ 0} :=
    isOpen_ne.preimage (ENNReal.continuous_ofReal.comp continuous_semicircleDensity)
  have hnhds : {y | ENNReal.ofReal (semicircleDensity y) ≠ 0} ∩ U ∈ 𝓝 x :=
    Filter.inter_mem (hopen.mem_nhds hn) hU
  have hp := (volume : Measure ℝ).measure_pos_of_mem_nhds hnhds
  exact hp.ne' hz

/-- The actual explicit semicircle measure has support exactly `[-2,2]`, including both endpoints. -/
theorem semicircleMeasure_support : semicircleMeasure.support = Icc (-2 : ℝ) 2 := by
  apply Subset.antisymm
  · exact Measure.support_subset_of_isClosed isClosed_Icc semicircleMeasure_Icc_compl
  · rw [← closure_Ioo (by norm_num : (-2 : ℝ) ≠ 2)]
    exact closure_minimal Ioo_subset_semicircleMeasure_support Measure.isClosed_support

end FreeProbability.Semicircular

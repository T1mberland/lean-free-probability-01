import FreeProbability.Semicircular.SpectralDensityIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # The genuine probability measure with the explicit variance-one semicircle density -/

noncomputable section
open scoped ENNReal
open MeasureTheory Set intervalIntegral

namespace FreeProbability.Semicircular

/-- Integration of a density-weighted function reduces exactly to its defining compact interval. -/
theorem integral_mul_semicircleDensity_eq_interval (f : ℝ → ℝ) :
    (∫ x : ℝ, f x * semicircleDensity x) = ∫ x in (-2 : ℝ)..2, f x * semicircleDensity x := by
  have he : (fun x : ℝ => f x * semicircleDensity x) =
      (Ioc (-2 : ℝ) 2).indicator (fun x => f x * semicircleDensity x) := by
    funext x
    by_cases hx : x ∈ Ioc (-2 : ℝ) 2
    · simp only [indicator_of_mem hx]
    · have hs : 4 - x ^ 2 ≤ 0 := by
        simp only [mem_Ioc, not_and_or, not_lt, not_le] at hx
        rcases hx with hx | hx <;> nlinarith
      have hd : semicircleDensity x = 0 := by
        simp [semicircleDensity, Real.sqrt_eq_zero_of_nonpos hs]
      simp [indicator_of_notMem hx, hd]
  conv_lhs => rw [he]
  rw [MeasureTheory.integral_indicator measurableSet_Ioc, integral_of_le (by norm_num : (-2 : ℝ) ≤ 2)]

/-- The explicit continuous density has genuinely compact support. -/
theorem hasCompactSupport_semicircleDensity : HasCompactSupport semicircleDensity := by
  have hs : Function.support semicircleDensity ⊆ Icc (-2 : ℝ) 2 := by
    intro x hx
    by_contra hn
    exact hx (semicircleDensity_eq_zero_of_notMem hn)
  exact isCompact_Icc.of_isClosed_subset isClosed_closure (closure_minimal hs isClosed_Icc)

theorem integrable_semicircleDensity : Integrable semicircleDensity (volume : Measure ℝ) :=
  continuous_semicircleDensity.integrable_of_hasCompactSupport hasCompactSupport_semicircleDensity

/-- The density integrates to one over the entire real line. -/
@[simp] theorem integral_semicircleDensity_realLine : (∫ x : ℝ, semicircleDensity x) = 1 := by
  simpa using (integral_mul_semicircleDensity_eq_interval (fun _ => 1)).trans
    (by simp)

/-- The actual Borel measure with density `sqrt(4-x²)/(2π)` against real Lebesgue measure. -/
def semicircleMeasure : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (semicircleDensity x))

instance : IsProbabilityMeasure semicircleMeasure where
  measure_univ := by
    rw [semicircleMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal integrable_semicircleDensity
      (Filter.Eventually.of_forall semicircleDensity_nonneg), integral_semicircleDensity_realLine]
    norm_num

/-- Integrating against the genuine density measure is the actual Lebesgue weighted integral. -/
theorem integral_semicircleMeasure (f : ℝ → ℝ) :
    (∫ x, f x ∂semicircleMeasure) = ∫ x in (-2 : ℝ)..2, f x * semicircleDensity x := by
  have hm : Measurable (fun x => ENNReal.ofReal (semicircleDensity x)) :=
    ENNReal.measurable_ofReal.comp continuous_semicircleDensity.measurable
  rw [semicircleMeasure, integral_withDensity_eq_integral_toReal_smul hm (by simp) f]
  simp only [ENNReal.toReal_ofReal (semicircleDensity_nonneg _), smul_eq_mul]
  simpa only [mul_comm] using integral_mul_semicircleDensity_eq_interval f

/-- Actual even moments of the explicit probability measure are Catalan numbers. -/
theorem semicircleMeasure_even_moment (n : ℕ) :
    (∫ x : ℝ, x ^ (2 * n) ∂semicircleMeasure) = (catalan n : ℝ) := by
  rw [integral_semicircleMeasure, integral_semicircleDensity_even]

/-- Actual odd moments of the explicit probability measure vanish. -/
theorem semicircleMeasure_odd_moment (n : ℕ) :
    (∫ x : ℝ, x ^ (2 * n + 1) ∂semicircleMeasure) = 0 := by
  rw [integral_semicircleMeasure, integral_semicircleDensity_odd]

/-- The explicit semicircle probability measure is concentrated on its defining compact interval. -/
theorem semicircleMeasure_Icc_compl : semicircleMeasure (Icc (-2 : ℝ) 2)ᶜ = 0 := by
  rw [semicircleMeasure, withDensity_apply _ measurableSet_Icc.compl]
  apply (lintegral_eq_zero_iff'
    (ENNReal.measurable_ofReal.comp continuous_semicircleDensity.measurable).aemeasurable).mpr
  filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with x hx
  simp only [Function.comp_apply, semicircleDensity_eq_zero_of_notMem hx, ENNReal.ofReal_zero, Pi.zero_apply]

end FreeProbability.Semicircular

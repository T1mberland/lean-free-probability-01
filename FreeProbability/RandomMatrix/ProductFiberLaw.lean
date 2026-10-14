import Mathlib.Probability.HasLaw

/-! # Constant fiber laws and exceptional-input bounds in product probability -/

namespace FreeProbability

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {Ω Γ E : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ] [MeasurableSpace E]

/-- A constant law on almost every fresh-noise fiber gives the full joint product
law with the past, hence independence from the past. -/
theorem hasLaw_prod_fst_of_fiber_law (μ : Measure Ω) (ν : Measure Γ) (ρ : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (F : Ω × Γ → E) (hF : Measurable F)
    (h : ∀ᵐ a ∂μ, HasLaw (fun b => F (a, b)) ρ ν) :
    HasLaw (fun p => (p.1, F p)) (μ.prod ρ) (μ.prod ν) := by
  refine ⟨(measurable_fst.prodMk hF).aemeasurable, ?_⟩
  apply (Measure.prod_eq ?_).symm
  intro A B hA hB
  rw [Measure.map_apply (measurable_fst.prodMk hF) (hA.prod hB),
    Measure.prod_apply ((measurable_fst.prodMk hF) (hA.prod hB))]
  calc
    _ = ∫⁻ a, A.indicator (fun _ => ρ B) a ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [h] with a ha
      by_cases haA : a ∈ A
      · have he : Prod.mk a ⁻¹' ((fun p : Ω × Γ => (p.1, F p)) ⁻¹' (A ×ˢ B)) =
            (fun b => F (a, b)) ⁻¹' B := by ext b; simp [haA]
        rw [he, indicator_of_mem haA]
        exact ha.measure_eq hB
      · have he : Prod.mk a ⁻¹' ((fun p : Ω × Γ => (p.1, F p)) ⁻¹' (A ×ˢ B)) = ∅ := by
          ext b
          simp [haA]
        simp [he, haA]
    _ = μ A * ρ B := by rw [lintegral_indicator_const hA, mul_comm]

/-- Fiber estimates remain valid for random inputs that may hit an exceptional
set: its probability is retained explicitly. -/
theorem measure_prod_event_le_of_fiber_bound (μ : Measure Ω) (ν : Measure Γ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (S : Set (Ω × Γ)) (hS : MeasurableSet S) (D : Set Ω) (hD : MeasurableSet D)
    (c : ℝ≥0∞) (h : ∀ a ∉ D, ν (Prod.mk a ⁻¹' S) ≤ c) :
    μ.prod ν S ≤ μ D + c := by
  rw [Measure.prod_apply hS]
  calc
    _ ≤ ∫⁻ a, D.indicator (fun _ => (1 : ℝ≥0∞)) a + c ∂μ := by
      apply lintegral_mono
      intro a
      change ν (Prod.mk a ⁻¹' S) ≤ D.indicator (fun _ => (1 : ℝ≥0∞)) a + c
      by_cases ha : a ∈ D
      · rw [indicator_of_mem ha]
        exact prob_le_one.trans le_self_add
      · rw [indicator_of_notMem ha, zero_add]
        exact h a ha
    _ = μ D + c := by
      rw [lintegral_add_left (measurable_const.indicator hD),
        lintegral_indicator_const hD, lintegral_const]
      simp

end FreeProbability

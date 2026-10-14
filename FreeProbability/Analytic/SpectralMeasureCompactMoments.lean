import FreeProbability.Analytic.SpectralMeasureUniqueness

/-! # Actual probability measures concentrated on a common compact set are determined by moments -/

noncomputable section
open scoped Classical CompactlySupported
open MeasureTheory Set

namespace FreeProbability

variable (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {K : Set ℝ} (hK : IsCompact K) (hμ : μ Kᶜ = 0) (hν : ν Kᶜ = 0)

/-- Compact concentration gives genuine integrability of every continuous function on that set. -/
theorem integrable_of_compact_concentration (hK : IsCompact K) (hμ : μ Kᶜ = 0) {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E) (hf : ContinuousOn f K) : Integrable f μ := by
  have hi := hf.integrableOn_compact hK (μ := μ)
  change Integrable f (μ.restrict K) at hi
  rwa [Measure.restrict_eq_self_of_ae_mem hμ] at hi

/-- Uniform approximation on the compact support controls actual integral errors. -/
theorem integral_polynomial_error_bound (hK : IsCompact K) (hμ : μ Kᶜ = 0) [CompactSpace K] (f : C(ℝ, ℝ)) (p : Polynomial ℝ) :
    ‖(∫ x, f x ∂μ) - ∫ x, p.eval x ∂μ‖ ≤
      ‖f.comp ⟨Subtype.val, continuous_subtype_val⟩ - Polynomial.toContinuousMapOnAlgHom K p‖ := by
  rw [← integral_sub (integrable_of_compact_concentration μ hK hμ f f.continuous.continuousOn)
    (integrable_of_compact_concentration μ hK hμ p.eval p.continuous.continuousOn)]
  have hb : ∀ᵐ x ∂μ, ‖f x - p.eval x‖ ≤
      ‖f.comp ⟨Subtype.val, continuous_subtype_val⟩ - Polynomial.toContinuousMapOnAlgHom K p‖ := by
    filter_upwards [show ∀ᵐ x ∂μ, x ∈ K from hμ] with x hx
    exact ContinuousMap.norm_coe_le_norm
      (f.comp ⟨Subtype.val, continuous_subtype_val⟩ - Polynomial.toContinuousMapOnAlgHom K p) ⟨x, hx⟩
  simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const hb

/-- Actual compactly concentrated probability measures are uniquely determined by all power moments. -/
theorem probabilityMeasure_eq_of_compact_power_moments (hK : IsCompact K) (hμ : μ Kᶜ = 0) (hν : ν Kᶜ = 0)
    (hm : ∀ n : ℕ, (∫ x : ℝ, x ^ n ∂μ) = ∫ x : ℝ, x ^ n ∂ν) : μ = ν := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hp : ∀ p : Polynomial ℝ, (∫ x, p.eval x ∂μ) = ∫ x, p.eval x ∂ν := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q ip iq =>
      simp only [Polynomial.eval_add]
      rw [integral_add (integrable_of_compact_concentration μ hK hμ p.eval p.continuous.continuousOn)
        (integrable_of_compact_concentration μ hK hμ q.eval q.continuous.continuousOn),
        integral_add (integrable_of_compact_concentration ν hK hν p.eval p.continuous.continuousOn)
        (integrable_of_compact_concentration ν hK hν q.eval q.continuous.continuousOn), ip, iq]
    | monomial n c =>
      simp only [Polynomial.eval_monomial, integral_const_mul, hm]
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    let g : C(K, ℝ) := f.toContinuousMap.comp ⟨Subtype.val, continuous_subtype_val⟩
    have hg : g ∈ closure (polynomialFunctions K : Set C(K, ℝ)) := by
      change g ∈ (polynomialFunctions K).topologicalClosure
      rw [polynomialFunctions.topologicalClosure]
      trivial
    obtain ⟨q, hq, hdist⟩ := Metric.mem_closure_iff.mp hg (ε / 3) (by positivity)
    rw [polynomialFunctions_coe] at hq
    obtain ⟨p, rfl⟩ := hq
    have hleft := integral_polynomial_error_bound μ hK hμ f.toContinuousMap p
    have hright := integral_polynomial_error_bound ν hK hν f.toContinuousMap p
    change ‖(∫ x, f x ∂μ) - ∫ x, p.eval x ∂μ‖ ≤
      ‖g - Polynomial.toContinuousMapOnAlgHom K p‖ at hleft
    change ‖(∫ x, f x ∂ν) - ∫ x, p.eval x ∂ν‖ ≤
      ‖g - Polynomial.toContinuousMapOnAlgHom K p‖ at hright
    rw [hp p] at hleft
    have happrox : ‖g - Polynomial.toContinuousMapOnAlgHom K p‖ < ε / 3 := by
      rwa [dist_eq_norm] at hdist
    have ht := norm_sub_le_norm_sub_add_norm_sub (∫ x, f x ∂μ) (∫ x, p.eval x ∂μ) (∫ x, f x ∂ν)
    rw [hp p, norm_sub_rev (∫ x, p.eval x ∂ν) (∫ x, f x ∂ν)] at ht
    change ‖(∫ x, f x ∂μ) - ∫ x, f x ∂ν‖ ≤ 0 + ε
    linarith
  · exact norm_nonneg _

end FreeProbability

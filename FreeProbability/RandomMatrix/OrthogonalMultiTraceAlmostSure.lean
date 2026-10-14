import FreeProbability.RandomMatrix.OrthogonalMultiTraceConvergence

/-! # Almost sure centered trace convergence from actual Haar marginals -/

noncomputable section
open scoped Classical Topology
namespace FreeProbability.Orthogonal
open Matrix MeasureTheory Filter ENNReal

private theorem ae_summable_norm_of_summable_integral
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (F : ℕ → Ω → ℝ)
    (hF : ∀ i, Integrable (F i) μ)
    (hs : Summable (fun i => ∫ x, ‖F i x‖ ∂μ)) :
    ∀ᵐ x ∂μ, Summable (fun i => ‖F i x‖) := by
  have he (i : ℕ) : ∫⁻ x, ‖F i x‖ₑ ∂μ = ‖∫ x, ‖F i x‖ ∂μ‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hF i).norm]
    simp only [coe_nnreal_eq, coe_nnnorm, Real.norm_eq_abs]
    rw [abs_of_nonneg (integral_nonneg (fun x => abs_nonneg (F i x)))]
  have hsum : ∑' i, ∫⁻ x, ‖F i x‖ₑ ∂μ ≠ ∞ := by
    rw [funext he]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 (NNReal.summable_coe.1 hs.abs)
  have hm (i : ℕ) : AEMeasurable (fun x => ‖F i x‖ₑ) μ := (hF i).1.enorm
  rw [← lintegral_tsum hm] at hsum
  refine (ae_lt_top' (AEMeasurable.tsum hm) hsum).mono ?_
  intro x hx
  change Summable (fun i => (‖F i x‖₊ : ℝ))
  rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
  exact hx.ne

/-- For any coupling with actual Haar marginals, centered uniformly bounded
trace words converge to zero almost surely. No independence between dimensions
is required. -/
theorem ae_centered_traceWord_tendsto {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {r : ℕ} (hr : 0 < r) (K : ℝ) (hK : 0 ≤ K)
    (A B : ∀ N : ℕ, Fin r → Matrix (Fin N) (Fin N) ℂ)
    (hA : ∀ N k, Matrix.trace (A N k) = 0) (hB : ∀ N k, Matrix.trace (B N k) = 0)
    (hAn : ∀ N k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A N k)‖ ≤ K)
    (hBn : ∀ N k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B N k)‖ ≤ K)
    (X : ∀ N : ℕ, Ω → Group (Fin N))
    (hX : ∀ N, MeasurePreserving (X N) μ (haar (Fin N))) :
    ∀ᵐ ω ∂μ, Tendsto (fun N => traceWord (A N) (B N) (X N ω)) atTop (𝓝 0) := by
  let F : ℕ → Ω → ℝ := fun N ω => ‖traceWord (A N) (B N) (X N ω)‖ ^ 2
  have hF (N : ℕ) : Integrable (F N) μ :=
    (hX N).integrable_comp_of_integrable (integrable_traceWord_norm_sq hr (A N) (B N))
  have hi (N : ℕ) : (∫ ω, ‖F N ω‖ ∂μ) = traceWordSecondMoment (A N) (B N) := by
    simp only [F, Real.norm_eq_abs, abs_sq]
    have hm := (integrable_traceWord_norm_sq hr (A N) (B N)).aestronglyMeasurable
    rw [← (hX N).map_eq] at hm
    rw [← integral_map (hX N).measurable.aemeasurable hm, (hX N).map_eq]
    rfl
  have hs : Summable (fun N => ∫ ω, ‖F N ω‖ ∂μ) := by
    simp_rw [hi]
    exact summable_centered_traceWordSecondMoment hr K hK A B hA hB hAn hBn
  filter_upwards [ae_summable_norm_of_summable_integral F hF hs] with ω hω
  have ht := hω.tendsto_atTop_zero
  simp only [F, Real.norm_eq_abs, abs_sq] at ht
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp ht
  change Tendsto (fun N => Real.sqrt (‖traceWord (A N) (B N) (X N ω)‖ ^ 2))
    atTop (𝓝 (Real.sqrt 0)) at hroot
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using hroot

end FreeProbability.Orthogonal

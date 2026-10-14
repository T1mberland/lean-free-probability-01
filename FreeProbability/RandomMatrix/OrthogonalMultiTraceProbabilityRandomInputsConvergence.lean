import FreeProbability.RandomMatrix.OrthogonalMultiTraceProbabilityIndependentInputs

/-! # Almost sure convergence for genuinely independent random inputs -/

noncomputable section
open scoped Classical Topology
namespace FreeProbability.Orthogonal
open Matrix MeasureTheory Filter ProbabilityTheory ENNReal

private theorem ae_summable_real_norm_of_integrals
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

/-- Summable genuine second absolute moments give actual almost sure
convergence to zero in any normed additive group. -/
theorem ae_tendsto_zero_of_summable_integral_norm_sq {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] (μ : Measure Ω) (F : ℕ → Ω → E)
    (hF : ∀ N, Integrable (fun ω => ‖F N ω‖ ^ 2) μ)
    (hs : Summable (fun N => ∫ ω, ‖F N ω‖ ^ 2 ∂μ)) :
    ∀ᵐ ω ∂μ, Tendsto (fun N => F N ω) atTop (𝓝 0) := by
  have hsn : Summable (fun N => ∫ ω, ‖‖F N ω‖ ^ 2‖ ∂μ) := by
    simpa only [Real.norm_eq_abs, abs_sq] using hs
  filter_upwards [ae_summable_real_norm_of_integrals (fun N ω => ‖F N ω‖ ^ 2) hF hsn] with ω hω
  have ht := hω.tendsto_atTop_zero
  simp only [Real.norm_eq_abs, abs_sq] at ht
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp ht
  change Tendsto (fun N => Real.sqrt (‖F N ω‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) at hroot
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using hroot

variable {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ] (μ : Measure Ω)

/-- Independent random inputs with actual uniformly bounded centered marginal
factors have true almost sure centered Haar trace convergence. Input laws may
vary with dimension, and no independence across dimensions is required. -/
theorem ae_independent_inputs_traceWord_tendsto {r : ℕ} (hr : 0 < r) (K : ℝ) (hK : 0 ≤ K)
    (A B : ∀ N : ℕ, Θ → Fin r → Matrix (Fin N) (Fin N) ℂ)
    (hAm : ∀ N, Measurable (A N)) (hBm : ∀ N, Measurable (B N))
    (Y : ℕ → Ω → Θ) (X : ∀ N : ℕ, Ω → Group (Fin N)) (hY : ∀ N, Measurable (Y N))
    (hX : ∀ N, MeasurePreserving (X N) μ (haar (Fin N))) (hi : ∀ N, IndepFun (Y N) (X N) μ)
    (hA : ∀ N, ∀ᵐ θ ∂μ.map (Y N), ∀ k, Matrix.trace (A N θ k) = 0)
    (hB : ∀ N, ∀ᵐ θ ∂μ.map (Y N), ∀ k, Matrix.trace (B N θ k) = 0)
    (hAn : ∀ N, ∀ᵐ θ ∂μ.map (Y N), ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A N θ k)‖ ≤ K)
    (hBn : ∀ N, ∀ᵐ θ ∂μ.map (Y N), ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B N θ k)‖ ≤ K) :
    ∀ᵐ ω ∂μ, Tendsto (fun N => traceWord (A N (Y N ω)) (B N (Y N ω)) (X N ω)) atTop (𝓝 0) := by
  apply ae_tendsto_zero_of_summable_integral_norm_sq
  · intro N
    exact integrable_independent_inputs_traceWord_norm_sq μ hr K hK (A N) (B N) (hAm N) (hBm N)
      (Y N) (X N) (hY N) (hX N) (hi N) (hAn N) (hBn N)
  · have hs : Summable (fun N : ℕ => ((N : ℝ)⁻¹) ^ 2) := by
      simpa only [inv_pow] using (Real.summable_nat_pow_inv.mpr (by decide : 1 < (2 : ℕ)))
    apply (hs.mul_left (orthogonalCenteredTraceConstant (r + r) * K ^ (2 * (r + r)))).of_norm_bounded_eventually_nat
    filter_upwards [eventually_independent_inputs_traceWordSecondMoment_bound (Θ := Θ) μ hr K hK] with N hN
    have hb := hN (A N) (B N) (Y N) (X N) (hAm N) (hBm N) (hY N) (hX N) (hi N)
      (hA N) (hB N) (hAn N) (hBn N)
    have hn : 0 ≤ ∫ ω, ‖traceWord (A N (Y N ω)) (B N (Y N ω)) (X N ω)‖ ^ 2 ∂μ :=
      integral_nonneg (fun ω => sq_nonneg _)
    simpa only [Real.norm_eq_abs, abs_of_nonneg hn] using hb

/-- The same genuine independent-input random words converge in probability. -/
theorem independent_inputs_traceWord_tendstoInMeasure {r : ℕ} (hr : 0 < r) (K : ℝ) (hK : 0 ≤ K)
    (A B : ∀ N : ℕ, Θ → Fin r → Matrix (Fin N) (Fin N) ℂ)
    (hAm : ∀ N, Measurable (A N)) (hBm : ∀ N, Measurable (B N))
    (Y : ℕ → Ω → Θ) (X : ∀ N : ℕ, Ω → Group (Fin N)) (hY : ∀ N, Measurable (Y N))
    (hX : ∀ N, MeasurePreserving (X N) μ (haar (Fin N))) (hi : ∀ N, IndepFun (Y N) (X N) μ)
    (hA : ∀ N, ∀ᵐ θ ∂μ.map (Y N), ∀ k, Matrix.trace (A N θ k) = 0)
    (hB : ∀ N, ∀ᵐ θ ∂μ.map (Y N), ∀ k, Matrix.trace (B N θ k) = 0)
    (hAn : ∀ N, ∀ᵐ θ ∂μ.map (Y N), ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A N θ k)‖ ≤ K)
    (hBn : ∀ N, ∀ᵐ θ ∂μ.map (Y N), ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B N θ k)‖ ≤ K) :
    TendstoInMeasure μ (fun N ω => traceWord (A N (Y N ω)) (B N (Y N ω)) (X N ω)) atTop (fun _ => 0) := by
  let : IsProbabilityMeasure μ := probabilityMeasure_of_haar_marginal μ (X 0) (hX 0)
  apply tendstoInMeasure_of_tendsto_ae
  · intro N
    exact (measurable_traceWord_inputs (n := Fin N) (r := r) (fun ω => A N (Y N ω))
      (fun ω => B N (Y N ω)) (X N) ((hAm N).comp (hY N)) ((hBm N).comp (hY N))
      (hX N).measurable).aestronglyMeasurable
  · exact ae_independent_inputs_traceWord_tendsto μ hr K hK A B hAm hBm Y X hY hX hi hA hB hAn hBn

end FreeProbability.Orthogonal

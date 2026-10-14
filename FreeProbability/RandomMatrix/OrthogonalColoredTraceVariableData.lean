import FreeProbability.RandomMatrix.OrthogonalColoredTraceWords

/-! # Genuine independent input convergence with dimension-dependent data types -/

noncomputable section
open scoped Classical Topology
namespace FreeProbability.Orthogonal
open Matrix MeasureTheory Filter ProbabilityTheory
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
variable (Θ : ℕ → Type*) [∀ N, MeasurableSpace (Θ N)]

/-- Actual centered random-input squared trace moments have a uniform tail
also when the entire data TYPE changes with dimension. -/
theorem eventually_variableData_traceWordSecondMoment_bound {r : ℕ} (hr : 0 < r) (K : ℝ) (hK : 0 ≤ K)
    (A B : ∀ N : ℕ, Θ N → Fin r → Matrix (Fin N) (Fin N) ℂ)
    (hAm : ∀ N, Measurable (A N)) (hBm : ∀ N, Measurable (B N))
    (Y : ∀ N : ℕ, Ω → Θ N) (X : ∀ N : ℕ, Ω → Group (Fin N)) (hY : ∀ N, Measurable (Y N))
    (hX : ∀ N, MeasurePreserving (X N) μ (haar (Fin N))) (hi : ∀ N, IndepFun (Y N) (X N) μ)
    (hA : ∀ N, ∀ᵐ θ ∂μ.map (Y N), ∀ k, Matrix.trace (A N θ k) = 0)
    (hB : ∀ N, ∀ᵐ θ ∂μ.map (Y N), ∀ k, Matrix.trace (B N θ k) = 0)
    (hAn : ∀ N, ∀ᵐ θ ∂μ.map (Y N), ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A N θ k)‖ ≤ K)
    (hBn : ∀ N, ∀ᵐ θ ∂μ.map (Y N), ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B N θ k)‖ ≤ K) :
    ∀ᶠ N : ℕ in atTop, (∫ ω, ‖traceWord (A N (Y N ω)) (B N (Y N ω)) (X N ω)‖ ^ 2 ∂μ) ≤
      orthogonalCenteredTraceConstant (r + r) * K ^ (2 * (r + r)) * ((N : ℝ)⁻¹) ^ 2 := by
  filter_upwards [eventually_centered_traceWordSecondMoment_bound hr K hK] with N hN
  let : IsProbabilityMeasure μ := probabilityMeasure_of_haar_marginal μ (X N) (hX N)
  rw [independent_inputs_traceWordSecondMoment_eq μ hr K hK (A N) (B N) (hAm N) (hBm N)
    (Y N) (X N) (hY N) (hX N) (hi N) (hAn N) (hBn N),
    randomInputsTraceWordSecondMoment_eq_integral (μ.map (Y N)) hr K hK
      (A N) (B N) (hAm N) (hBm N) (hAn N) (hBn N)]
  have hprod := integrable_randomInputsTraceWord_norm_sq (μ.map (Y N)) hr K hK
    (A N) (B N) (hAm N) (hBm N) (hAn N) (hBn N)
  have hb : ∀ᵐ θ ∂μ.map (Y N), traceWordSecondMoment (A N θ) (B N θ) ≤
      orthogonalCenteredTraceConstant (r + r) * K ^ (2 * (r + r)) * ((N : ℝ)⁻¹) ^ 2 := by
    filter_upwards [hA N, hB N, hAn N, hBn N] with θ hcA hcB hnA hnB
    exact hN (A N θ) (B N θ) hcA hcB hnA hnB
  simpa only [randomInputsTraceWord, traceWordSecondMoment, integral_const, Measure.real,
    measure_univ, ENNReal.toReal_one, one_smul] using
    integral_mono_ae hprod.integral_prod_left (integrable_const _) hb

/-- Almost sure centered trace convergence for genuine independent random
data of dimension-dependent types. No cross-dimension independence is imposed. -/
theorem ae_variableData_traceWord_tendsto {r : ℕ} (hr : 0 < r) (K : ℝ) (hK : 0 ≤ K)
    (A B : ∀ N : ℕ, Θ N → Fin r → Matrix (Fin N) (Fin N) ℂ)
    (hAm : ∀ N, Measurable (A N)) (hBm : ∀ N, Measurable (B N))
    (Y : ∀ N : ℕ, Ω → Θ N) (X : ∀ N : ℕ, Ω → Group (Fin N)) (hY : ∀ N, Measurable (Y N))
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
    filter_upwards [eventually_variableData_traceWordSecondMoment_bound μ Θ hr K hK
      A B hAm hBm Y X hY hX hi hA hB hAn hBn] with N hN
    have hn : 0 ≤ ∫ ω, ‖traceWord (A N (Y N ω)) (B N (Y N ω)) (X N ω)‖ ^ 2 ∂μ :=
      integral_nonneg (fun _ => sq_nonneg _)
    simpa only [Real.norm_eq_abs, abs_of_nonneg hn] using hN

/-- The same actual theorem with all data centering and bounds stated on
sampled inputs in the original source space. -/
theorem ae_variableData_traceWord_tendsto_of_source {r : ℕ} (hr : 0 < r) (K : ℝ) (hK : 0 ≤ K)
    (A B : ∀ N : ℕ, Θ N → Fin r → Matrix (Fin N) (Fin N) ℂ)
    (hAm : ∀ N, Measurable (A N)) (hBm : ∀ N, Measurable (B N))
    (Y : ∀ N : ℕ, Ω → Θ N) (X : ∀ N : ℕ, Ω → Group (Fin N)) (hY : ∀ N, Measurable (Y N))
    (hX : ∀ N, MeasurePreserving (X N) μ (haar (Fin N))) (hi : ∀ N, IndepFun (Y N) (X N) μ)
    (hA : ∀ N, ∀ᵐ ω ∂μ, ∀ k, Matrix.trace (A N (Y N ω) k) = 0)
    (hB : ∀ N, ∀ᵐ ω ∂μ, ∀ k, Matrix.trace (B N (Y N ω) k) = 0)
    (hAn : ∀ N, ∀ᵐ ω ∂μ, ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A N (Y N ω) k)‖ ≤ K)
    (hBn : ∀ N, ∀ᵐ ω ∂μ, ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B N (Y N ω) k)‖ ≤ K) :
    ∀ᵐ ω ∂μ, Tendsto (fun N => traceWord (A N (Y N ω)) (B N (Y N ω)) (X N ω)) atTop (𝓝 0) := by
  apply ae_variableData_traceWord_tendsto μ Θ hr K hK A B hAm hBm Y X hY hX hi
  · intro N
    exact (ae_centered_inputs_map_iff μ (A N) (hAm N) (Y N) (hY N)).mpr (hA N)
  · intro N
    exact (ae_centered_inputs_map_iff μ (B N) (hBm N) (Y N) (hY N)).mpr (hB N)
  · intro N
    exact (ae_bounded_inputs_map_iff μ (A N) (hAm N) (Y N) (hY N) K).mpr (hAn N)
  · intro N
    exact (ae_bounded_inputs_map_iff μ (B N) (hBm N) (Y N) (hY N) K).mpr (hBn N)

/-- Actual convergence in probability also allows a different data type in
each dimension, with the same natural source-almost-everywhere hypotheses. -/
theorem variableData_traceWord_tendstoInMeasure_of_source {r : ℕ} (hr : 0 < r) (K : ℝ) (hK : 0 ≤ K)
    (A B : ∀ N : ℕ, Θ N → Fin r → Matrix (Fin N) (Fin N) ℂ)
    (hAm : ∀ N, Measurable (A N)) (hBm : ∀ N, Measurable (B N))
    (Y : ∀ N : ℕ, Ω → Θ N) (X : ∀ N : ℕ, Ω → Group (Fin N)) (hY : ∀ N, Measurable (Y N))
    (hX : ∀ N, MeasurePreserving (X N) μ (haar (Fin N))) (hi : ∀ N, IndepFun (Y N) (X N) μ)
    (hA : ∀ N, ∀ᵐ ω ∂μ, ∀ k, Matrix.trace (A N (Y N ω) k) = 0)
    (hB : ∀ N, ∀ᵐ ω ∂μ, ∀ k, Matrix.trace (B N (Y N ω) k) = 0)
    (hAn : ∀ N, ∀ᵐ ω ∂μ, ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A N (Y N ω) k)‖ ≤ K)
    (hBn : ∀ N, ∀ᵐ ω ∂μ, ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B N (Y N ω) k)‖ ≤ K) :
    TendstoInMeasure μ (fun N ω => traceWord (A N (Y N ω)) (B N (Y N ω)) (X N ω)) atTop (fun _ => 0) := by
  let : IsProbabilityMeasure μ := probabilityMeasure_of_haar_marginal μ (X 0) (hX 0)
  apply tendstoInMeasure_of_tendsto_ae
  · intro N
    exact (measurable_traceWord_inputs (n := Fin N) (r := r) (fun ω => A N (Y N ω))
      (fun ω => B N (Y N ω)) (X N) ((hAm N).comp (hY N)) ((hBm N).comp (hY N))
      (hX N).measurable).aestronglyMeasurable
  · exact ae_variableData_traceWord_tendsto_of_source μ Θ hr K hK A B hAm hBm Y X hY hX hi hA hB hAn hBn

end FreeProbability.Orthogonal

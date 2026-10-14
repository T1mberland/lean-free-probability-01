import FreeProbability.RandomMatrix.OrthogonalMultiTraceProbabilityRandomInputsConvergence

/-! # Source and marginal hypotheses for actual random matrix inputs -/

noncomputable section
open scoped Classical Topology
namespace FreeProbability.Orthogonal
open Matrix MeasureTheory Filter ProbabilityTheory
variable {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ] (μ : Measure Ω)
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
private theorem measurable_matrix_trace (A : Θ → Matrix n n ℂ) (hA : Measurable A) :
    Measurable (fun θ => Matrix.trace (A θ)) := by
  unfold Matrix.trace
  apply Finset.measurable_sum
  intro k _
  exact hA.eval_matrix

private theorem measurable_Euclidean_opNorm :
    Measurable (fun A : Matrix n n ℂ => ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖) := by
  have hc : Continuous (fun A : Matrix n n ℂ => ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖) := by
    open scoped Matrix.Norms.L2Operator in
      simpa only [Matrix.cstar_norm_def] using (continuous_norm : Continuous (fun A : Matrix n n ℂ => ‖A‖))
  exact hc.measurable

omit [DecidableEq n] in
/-- Genuine marginal centering is equivalent to actual source-almost-everywhere centering. -/
theorem ae_centered_inputs_map_iff {r : ℕ} (A : Θ → Fin r → Matrix n n ℂ)
    (hA : Measurable A) (Y : Ω → Θ) (hY : Measurable Y) :
    (∀ᵐ θ ∂μ.map Y, ∀ k, Matrix.trace (A θ k) = 0) ↔
      (∀ᵐ ω ∂μ, ∀ k, Matrix.trace (A (Y ω) k) = 0) := by
  apply ae_map_iff hY.aemeasurable
  have he : {θ | ∀ k, Matrix.trace (A θ k) = 0} = ⋂ k, {θ | Matrix.trace (A θ k) = 0} := by
    ext θ
    simp
  rw [he]
  apply MeasurableSet.iInter
  intro k
  exact measurableSet_eq_fun (measurable_matrix_trace _ hA.eval) measurable_const

/-- Literal operator bounds on the actual marginal are exactly the corresponding
source-almost-everywhere bounds, not an extra distributional assumption. -/
theorem ae_bounded_inputs_map_iff {r : ℕ} (A : Θ → Fin r → Matrix n n ℂ)
    (hA : Measurable A) (Y : Ω → Θ) (hY : Measurable Y) (K : ℝ) :
    (∀ᵐ θ ∂μ.map Y, ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A θ k)‖ ≤ K) ↔
      (∀ᵐ ω ∂μ, ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A (Y ω) k)‖ ≤ K) := by
  apply ae_map_iff hY.aemeasurable
  have he : {θ | ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A θ k)‖ ≤ K} =
      ⋂ k, {θ | ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A θ k)‖ ≤ K} := by
    ext θ
    simp
  rw [he]
  apply MeasurableSet.iInter
  intro k
  exact measurableSet_le ((measurable_Euclidean_opNorm (n := n)).comp hA.eval) measurable_const

/-- The actual independent-input almost sure theorem with all centering and
operator bounds stated directly on the original random realization. -/
theorem ae_independent_inputs_traceWord_tendsto_of_source {r : ℕ}
    (hr : 0 < r) (K : ℝ) (hK : 0 ≤ K)
    (A B : ∀ N : ℕ, Θ → Fin r → Matrix (Fin N) (Fin N) ℂ)
    (hAm : ∀ N, Measurable (A N)) (hBm : ∀ N, Measurable (B N))
    (Y : ℕ → Ω → Θ) (X : ∀ N : ℕ, Ω → Group (Fin N)) (hY : ∀ N, Measurable (Y N))
    (hX : ∀ N, MeasurePreserving (X N) μ (haar (Fin N))) (hi : ∀ N, IndepFun (Y N) (X N) μ)
    (hA : ∀ N, ∀ᵐ ω ∂μ, ∀ k, Matrix.trace (A N (Y N ω) k) = 0)
    (hB : ∀ N, ∀ᵐ ω ∂μ, ∀ k, Matrix.trace (B N (Y N ω) k) = 0)
    (hAn : ∀ N, ∀ᵐ ω ∂μ, ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A N (Y N ω) k)‖ ≤ K)
    (hBn : ∀ N, ∀ᵐ ω ∂μ, ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B N (Y N ω) k)‖ ≤ K) :
    ∀ᵐ ω ∂μ, Tendsto (fun N => traceWord (A N (Y N ω)) (B N (Y N ω)) (X N ω)) atTop (𝓝 0) := by
  apply ae_independent_inputs_traceWord_tendsto μ hr K hK A B hAm hBm Y X hY hX hi
  · intro N
    exact (ae_centered_inputs_map_iff μ (A N) (hAm N) (Y N) (hY N)).mpr (hA N)
  · intro N
    exact (ae_centered_inputs_map_iff μ (B N) (hBm N) (Y N) (hY N)).mpr (hB N)
  · intro N
    exact (ae_bounded_inputs_map_iff μ (A N) (hAm N) (Y N) (hY N) K).mpr (hAn N)
  · intro N
    exact (ae_bounded_inputs_map_iff μ (B N) (hBm N) (Y N) (hY N) K).mpr (hBn N)

/-- Source-almost-everywhere centered bounded independent inputs also give
actual convergence in probability. -/
theorem independent_inputs_traceWord_tendstoInMeasure_of_source {r : ℕ}
    (hr : 0 < r) (K : ℝ) (hK : 0 ≤ K)
    (A B : ∀ N : ℕ, Θ → Fin r → Matrix (Fin N) (Fin N) ℂ)
    (hAm : ∀ N, Measurable (A N)) (hBm : ∀ N, Measurable (B N))
    (Y : ℕ → Ω → Θ) (X : ∀ N : ℕ, Ω → Group (Fin N)) (hY : ∀ N, Measurable (Y N))
    (hX : ∀ N, MeasurePreserving (X N) μ (haar (Fin N))) (hi : ∀ N, IndepFun (Y N) (X N) μ)
    (hA : ∀ N, ∀ᵐ ω ∂μ, ∀ k, Matrix.trace (A N (Y N ω) k) = 0)
    (hB : ∀ N, ∀ᵐ ω ∂μ, ∀ k, Matrix.trace (B N (Y N ω) k) = 0)
    (hAn : ∀ N, ∀ᵐ ω ∂μ, ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A N (Y N ω) k)‖ ≤ K)
    (hBn : ∀ N, ∀ᵐ ω ∂μ, ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B N (Y N ω) k)‖ ≤ K) :
    TendstoInMeasure μ (fun N ω => traceWord (A N (Y N ω)) (B N (Y N ω)) (X N ω)) atTop (fun _ => 0) := by
  apply independent_inputs_traceWord_tendstoInMeasure μ hr K hK A B hAm hBm Y X hY hX hi
  · intro N
    exact (ae_centered_inputs_map_iff μ (A N) (hAm N) (Y N) (hY N)).mpr (hA N)
  · intro N
    exact (ae_centered_inputs_map_iff μ (B N) (hBm N) (Y N) (hY N)).mpr (hB N)
  · intro N
    exact (ae_bounded_inputs_map_iff μ (A N) (hAm N) (Y N) (hY N) K).mpr (hAn N)
  · intro N
    exact (ae_bounded_inputs_map_iff μ (B N) (hBm N) (Y N) (hY N) K).mpr (hBn N)

/-- A countable collection of centered random input words converges on one
actual full-measure set. Neither a common degree nor a common bound across
words nor independence across dimensions is imposed. -/
theorem ae_countable_independent_inputs_traceWords_tendsto_of_source {ι : Type*} [Countable ι]
    (r : ι → ℕ) (hr : ∀ i, 0 < r i) (K : ι → ℝ) (hK : ∀ i, 0 ≤ K i)
    (A B : ∀ i : ι, ∀ N : ℕ, Θ → Fin (r i) → Matrix (Fin N) (Fin N) ℂ)
    (hAm : ∀ i N, Measurable (A i N)) (hBm : ∀ i N, Measurable (B i N))
    (Y : ℕ → Ω → Θ) (X : ∀ N : ℕ, Ω → Group (Fin N)) (hY : ∀ N, Measurable (Y N))
    (hX : ∀ N, MeasurePreserving (X N) μ (haar (Fin N))) (hi : ∀ N, IndepFun (Y N) (X N) μ)
    (hA : ∀ i N, ∀ᵐ ω ∂μ, ∀ k, Matrix.trace (A i N (Y N ω) k) = 0)
    (hB : ∀ i N, ∀ᵐ ω ∂μ, ∀ k, Matrix.trace (B i N (Y N ω) k) = 0)
    (hAn : ∀ i N, ∀ᵐ ω ∂μ, ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A i N (Y N ω) k)‖ ≤ K i)
    (hBn : ∀ i N, ∀ᵐ ω ∂μ, ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B i N (Y N ω) k)‖ ≤ K i) :
    ∀ᵐ ω ∂μ, ∀ i, Tendsto (fun N => traceWord (A i N (Y N ω)) (B i N (Y N ω)) (X N ω)) atTop (𝓝 0) := by
  exact ae_all_iff.mpr (fun i => ae_independent_inputs_traceWord_tendsto_of_source μ (hr i) (K i) (hK i)
    (A i) (B i) (hAm i) (hBm i) Y X hY hX hi (hA i) (hB i) (hAn i) (hBn i))

end FreeProbability.Orthogonal

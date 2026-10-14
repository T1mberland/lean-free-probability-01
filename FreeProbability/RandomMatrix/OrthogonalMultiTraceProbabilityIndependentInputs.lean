import FreeProbability.RandomMatrix.OrthogonalMultiTraceProbabilityRandomInputs
import Mathlib.Probability.Independence.Basic

/-! # Actual independence transfers Haar product-law second moments -/

noncomputable section
open scoped Classical Topology
namespace FreeProbability.Orthogonal
open Matrix MeasureTheory Filter ProbabilityTheory
variable {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ] (μ : Measure Ω)
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Actual probabilistic independence and a Haar marginal give the genuine
joint product law of the input data and the orthogonal matrix. -/
theorem independent_inputs_haar_measurePreserving (Y : Ω → Θ) (X : Ω → Group n)
    (hY : Measurable Y) (hX : MeasurePreserving X μ (haar n)) (hi : IndepFun Y X μ) :
    MeasurePreserving (fun ω => (Y ω, X ω)) μ ((μ.map Y).prod (haar n)) := by
  let : IsProbabilityMeasure μ := probabilityMeasure_of_haar_marginal μ X hX
  refine ⟨hY.prodMk hX.measurable, ?_⟩
  rw [hi.map_prod_eq_prod_map_map hY.aemeasurable hX.measurable.aemeasurable, hX.map_eq]

/-- The actual squared trace integral in any independent-input realization
is the genuine product-law squared trace integral. -/
theorem independent_inputs_traceWordSecondMoment_eq {r : ℕ} (hr : 0 < r) (K : ℝ) (hK : 0 ≤ K)
    (A B : Θ → Fin r → Matrix n n ℂ) (hAm : Measurable A) (hBm : Measurable B)
    (Y : Ω → Θ) (X : Ω → Group n) (hY : Measurable Y)
    (hX : MeasurePreserving X μ (haar n)) (hi : IndepFun Y X μ)
    (hAn : ∀ᵐ θ ∂μ.map Y, ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A θ k)‖ ≤ K)
    (hBn : ∀ᵐ θ ∂μ.map Y, ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B θ k)‖ ≤ K) :
    (∫ ω, ‖traceWord (A (Y ω)) (B (Y ω)) (X ω)‖ ^ 2 ∂μ) =
      randomInputsTraceWordSecondMoment (μ.map Y) A B := by
  let : IsProbabilityMeasure μ := probabilityMeasure_of_haar_marginal μ X hX
  have hp := independent_inputs_haar_measurePreserving μ Y X hY hX hi
  have hm := (integrable_randomInputsTraceWord_norm_sq (μ.map Y) hr K hK A B hAm hBm hAn hBn).1
  rw [← hp.map_eq] at hm
  simpa only [hp.map_eq, randomInputsTraceWordSecondMoment, randomInputsTraceWord] using
    (integral_map hp.measurable.aemeasurable hm).symm

/-- Independence also transfers genuine squared-trace integrability; no
conditional expectation or integrability estimate is assumed. -/
theorem integrable_independent_inputs_traceWord_norm_sq {r : ℕ} (hr : 0 < r) (K : ℝ) (hK : 0 ≤ K)
    (A B : Θ → Fin r → Matrix n n ℂ) (hAm : Measurable A) (hBm : Measurable B)
    (Y : Ω → Θ) (X : Ω → Group n) (hY : Measurable Y)
    (hX : MeasurePreserving X μ (haar n)) (hi : IndepFun Y X μ)
    (hAn : ∀ᵐ θ ∂μ.map Y, ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A θ k)‖ ≤ K)
    (hBn : ∀ᵐ θ ∂μ.map Y, ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B θ k)‖ ≤ K) :
    Integrable (fun ω => ‖traceWord (A (Y ω)) (B (Y ω)) (X ω)‖ ^ 2) μ := by
  let : IsProbabilityMeasure μ := probabilityMeasure_of_haar_marginal μ X hX
  exact (independent_inputs_haar_measurePreserving μ Y X hY hX hi).integrable_comp_of_integrable
    (integrable_randomInputsTraceWord_norm_sq (μ.map Y) hr K hK A B hAm hBm hAn hBn)

/-- A single degree-dependent threshold works for all independent random
input laws and realizations, even when their distributions vary with dimension. -/
theorem eventually_independent_inputs_traceWordSecondMoment_bound {r : ℕ}
    (hr : 0 < r) (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ N : ℕ in atTop, ∀ (A B : Θ → Fin r → Matrix (Fin N) (Fin N) ℂ)
      (Y : Ω → Θ) (X : Ω → Group (Fin N)),
      Measurable A → Measurable B → Measurable Y →
      MeasurePreserving X μ (haar (Fin N)) → IndepFun Y X μ →
      (∀ᵐ θ ∂μ.map Y, ∀ k, Matrix.trace (A θ k) = 0) →
      (∀ᵐ θ ∂μ.map Y, ∀ k, Matrix.trace (B θ k) = 0) →
      (∀ᵐ θ ∂μ.map Y, ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A θ k)‖ ≤ K) →
      (∀ᵐ θ ∂μ.map Y, ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B θ k)‖ ≤ K) →
      (∫ ω, ‖traceWord (A (Y ω)) (B (Y ω)) (X ω)‖ ^ 2 ∂μ) ≤
        orthogonalCenteredTraceConstant (r + r) * K ^ (2 * (r + r)) * ((N : ℝ)⁻¹) ^ 2 := by
  filter_upwards [eventually_centered_traceWordSecondMoment_bound hr K hK] with N hN
  intro A B Y X hAm hBm hY hX hi hA hB hAn hBn
  let : IsProbabilityMeasure μ := probabilityMeasure_of_haar_marginal μ X hX
  rw [independent_inputs_traceWordSecondMoment_eq μ hr K hK A B hAm hBm Y X hY hX hi hAn hBn,
    randomInputsTraceWordSecondMoment_eq_integral (μ.map Y) hr K hK A B hAm hBm hAn hBn]
  have hprod := integrable_randomInputsTraceWord_norm_sq (μ.map Y) hr K hK A B hAm hBm hAn hBn
  have hb : ∀ᵐ θ ∂μ.map Y, traceWordSecondMoment (A θ) (B θ) ≤
      orthogonalCenteredTraceConstant (r + r) * K ^ (2 * (r + r)) * ((N : ℝ)⁻¹) ^ 2 := by
    filter_upwards [hA, hB, hAn, hBn] with θ hcA hcB hnA hnB
    exact hN (A θ) (B θ) hcA hcB hnA hnB
  simpa only [randomInputsTraceWord, traceWordSecondMoment, integral_const, Measure.real,
    measure_univ, ENNReal.toReal_one, one_smul] using
    integral_mono_ae hprod.integral_prod_left (integrable_const _) hb

end FreeProbability.Orthogonal

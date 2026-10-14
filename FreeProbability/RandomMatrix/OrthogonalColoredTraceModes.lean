import FreeProbability.RandomMatrix.OrthogonalColoredTraceCriterion

/-! # Genuine probability modes for the centered colored trace criterion -/

noncomputable section
open scoped Classical Topology
namespace FreeProbability.Orthogonal
open Matrix MeasureTheory Filter ProbabilityTheory

/-- Actual normalized colored trace observables are genuinely measurable. -/
theorem measurable_coloredTraceWord_inputs {Ω α I n : Type*} [MeasurableSpace Ω]
    [Fintype n] [DecidableEq n] (color : α → I) (word : List α)
    (A : Ω → α → Matrix n n ℂ) (U : Ω → I → Group n) (hA : Measurable A) (hU : Measurable U) :
    Measurable (fun ω => coloredTraceWord color word (A ω) (U ω)) := by
  have hp := measurable_coloredWordProduct color word A U hA hU
  unfold coloredTraceWord normalizedTrace Matrix.trace
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro i _
  exact hp.eval_matrix

section Modes
variable {Ω α I : Type*} [MeasurableSpace Ω] [Fintype I]
variable (μ : Measure Ω) (Θ : ℕ → Type*) [∀ N, MeasurableSpace (Θ N)]
variable (color : α → I) (word : List α) (hw : word ≠ [])
variable (halt : word.IsChain (fun a b => color a ≠ color b)) (K : ℝ) (hK : 0 ≤ K)
variable (A : ∀ N : ℕ, Θ N → α → Matrix (Fin N) (Fin N) ℂ) (hAm : ∀ N, Measurable (A N))
variable (Y : ∀ N : ℕ, Ω → Θ N) (X : ∀ N : ℕ, I → Ω → Group (Fin N))
variable (hY : ∀ N, Measurable (Y N)) (hX : ∀ N d, MeasurePreserving (X N d) μ (haar (Fin N)))
variable (hi : ∀ N, iIndepFun (augmentedHaarVariables (Y N) (X N)) μ)
variable (hA : ∀ N, ∀ᵐ ω ∂μ, ∀ a ∈ word, Matrix.trace (A N (Y N ω) a) = 0)
variable (hAn : ∀ N, ∀ᵐ ω ∂μ, ∀ a ∈ word, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A N (Y N ω) a)‖ ≤ K)

include hw halt K hK hAm hY hX hi hA hAn

/-- The genuine Haar marginal supplies coordinate measurability, so it need
not be repeated as an independent assumption in the actual almost sure criterion. -/
theorem ae_coloredTraceWord_tendsto_of_haar :
    ∀ᵐ ω ∂μ, Tendsto (fun N => coloredTraceWord color word (A N (Y N ω)) (fun d => X N d ω)) atTop (𝓝 0) :=
  ae_coloredTraceWord_tendsto μ Θ color word hw halt K hK A hAm Y X hY
    (fun N d => (hX N d).measurable) hX hi hA hAn

/-- Actual centered colored traces converge in probability under the same
joint random hypotheses and actual source-almost-everywhere operator bounds. -/
theorem coloredTraceWord_tendstoInMeasure :
    TendstoInMeasure μ (fun N ω => coloredTraceWord color word (A N (Y N ω)) (fun d => X N d ω))
      atTop (fun _ => 0) := by
  let : IsProbabilityMeasure μ := probabilityMeasure_of_haar_marginal μ (X 0 (color (word.head hw)))
    (hX 0 (color (word.head hw)))
  apply tendstoInMeasure_of_tendsto_ae
  · intro N
    exact (measurable_coloredTraceWord_inputs color word (fun ω => A N (Y N ω))
      (fun ω d => X N d ω) ((hAm N).comp (hY N))
      (measurable_pi_iff.mpr (fun d => (hX N d).measurable))).aestronglyMeasurable
  · exact ae_coloredTraceWord_tendsto_of_haar μ Θ color word hw halt K hK A hAm Y X hY hX hi hA hAn

/-- Actual expected normalized colored traces tend to zero, proved by the
actual almost sure criterion and genuine uniform domination, not a mean-limit premise. -/
theorem tendsto_expected_coloredTraceWord :
    Tendsto (fun N => ∫ ω, coloredTraceWord color word (A N (Y N ω)) (fun d => X N d ω) ∂μ)
      atTop (𝓝 0) := by
  let : IsProbabilityMeasure μ := probabilityMeasure_of_haar_marginal μ (X 0 (color (word.head hw)))
    (hX 0 (color (word.head hw)))
  have hm (N : ℕ) : AEStronglyMeasurable
      (fun ω => coloredTraceWord color word (A N (Y N ω)) (fun d => X N d ω)) μ :=
    (measurable_coloredTraceWord_inputs color word (fun ω => A N (Y N ω))
      (fun ω d => X N d ω) ((hAm N).comp (hY N))
      (measurable_pi_iff.mpr (fun d => (hX N d).measurable))).aestronglyMeasurable
  have hb (N : ℕ) : ∀ᵐ ω ∂μ,
      ‖coloredTraceWord color word (A N (Y N ω)) (fun d => X N d ω)‖ ≤ K ^ word.length := by
    filter_upwards [hAn N] with ω hω
    exact coloredTraceWord_norm_le color word _ _ K hK hω
  have hl := ae_coloredTraceWord_tendsto_of_haar μ Θ color word hw halt K hK A hAm Y X hY hX hi hA hAn
  have ht := tendsto_integral_of_dominated_convergence (fun _ : Ω => K ^ word.length) hm (integrable_const _) hb hl
  simpa only [integral_zero] using ht

end Modes

/-- A countable collection of actual alternating colored words converges on
one common full-measure set. Bounds may vary with the word. -/
theorem ae_countable_coloredTraceWords_tendsto {Ω α I J : Type*} [MeasurableSpace Ω]
    [Fintype I] [Countable J] (μ : Measure Ω) (Θ : ℕ → Type*) [∀ N, MeasurableSpace (Θ N)]
    (color : α → I) (word : J → List α) (hw : ∀ j, word j ≠ [])
    (halt : ∀ j, (word j).IsChain (fun a b => color a ≠ color b)) (K : J → ℝ) (hK : ∀ j, 0 ≤ K j)
    (A : ∀ N : ℕ, Θ N → α → Matrix (Fin N) (Fin N) ℂ) (hAm : ∀ N, Measurable (A N))
    (Y : ∀ N : ℕ, Ω → Θ N) (X : ∀ N : ℕ, I → Ω → Group (Fin N))
    (hY : ∀ N, Measurable (Y N)) (hX : ∀ N d, MeasurePreserving (X N d) μ (haar (Fin N)))
    (hi : ∀ N, iIndepFun (augmentedHaarVariables (Y N) (X N)) μ)
    (hA : ∀ j N, ∀ᵐ ω ∂μ, ∀ a ∈ word j, Matrix.trace (A N (Y N ω) a) = 0)
    (hAn : ∀ j N, ∀ᵐ ω ∂μ, ∀ a ∈ word j, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A N (Y N ω) a)‖ ≤ K j) :
    ∀ᵐ ω ∂μ, ∀ j, Tendsto (fun N => coloredTraceWord color (word j) (A N (Y N ω)) (fun d => X N d ω))
      atTop (𝓝 0) :=
  ae_all_iff.mpr (fun j => ae_coloredTraceWord_tendsto_of_haar μ Θ color (word j) (hw j) (halt j)
    (K j) (hK j) A hAm Y X hY hX hi (hA j) (hAn j))

end FreeProbability.Orthogonal

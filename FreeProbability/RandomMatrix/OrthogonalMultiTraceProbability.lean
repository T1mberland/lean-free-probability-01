import FreeProbability.RandomMatrix.OrthogonalMultiTraceAlmostSure
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Actual probability modes and countably many Haar trace words -/

noncomputable section
open scoped Classical Topology
namespace FreeProbability.Orthogonal
open Matrix MeasureTheory Filter

/-- An actual normalized Haar marginal already forces the source measure to
be a probability measure; this is not an extra random-model hypothesis. -/
theorem probabilityMeasure_of_haar_marginal {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {n : Type*} [Fintype n] [DecidableEq n] (X : Ω → Group n)
    (hX : MeasurePreserving X μ (haar n)) : IsProbabilityMeasure μ := by
  let : IsProbabilityMeasure (μ.map X) := by
    rw [hX.map_eq]
    infer_instance
  exact Measure.isProbabilityMeasure_of_map hX.measurable.aemeasurable

/-- Actual centered normalized trace words converge in probability under
uniform genuine operator bounds and actual Haar marginals. -/
theorem centered_traceWord_tendstoInMeasure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {r : ℕ} (hr : 0 < r) (K : ℝ) (hK : 0 ≤ K)
    (A B : ∀ N : ℕ, Fin r → Matrix (Fin N) (Fin N) ℂ)
    (hA : ∀ N k, Matrix.trace (A N k) = 0) (hB : ∀ N k, Matrix.trace (B N k) = 0)
    (hAn : ∀ N k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A N k)‖ ≤ K)
    (hBn : ∀ N k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B N k)‖ ≤ K)
    (X : ∀ N : ℕ, Ω → Group (Fin N))
    (hX : ∀ N, MeasurePreserving (X N) μ (haar (Fin N))) :
    TendstoInMeasure μ (fun N ω => traceWord (A N) (B N) (X N ω)) atTop (fun _ => 0) := by
  let : IsProbabilityMeasure μ := probabilityMeasure_of_haar_marginal μ (X 0) (hX 0)
  apply tendstoInMeasure_of_tendsto_ae
  · intro N
    exact ((hX N).integrable_comp_of_integrable (integrable_traceWord (A N) (B N))).1
  · exact ae_centered_traceWord_tendsto μ hr K hK A B hA hB hAn hBn X hX

/-- A countable collection of actual centered fixed words converges on ONE
full-measure set. Word degrees and operator bounds may vary across the collection. -/
theorem ae_countable_centered_traceWords_tendsto {Ω ι : Type*} [MeasurableSpace Ω]
    [Countable ι] (μ : Measure Ω) (r : ι → ℕ) (hr : ∀ i, 0 < r i)
    (K : ι → ℝ) (hK : ∀ i, 0 ≤ K i)
    (A B : ∀ i : ι, ∀ N : ℕ, Fin (r i) → Matrix (Fin N) (Fin N) ℂ)
    (hA : ∀ i N k, Matrix.trace (A i N k) = 0)
    (hB : ∀ i N k, Matrix.trace (B i N k) = 0)
    (hAn : ∀ i N k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A i N k)‖ ≤ K i)
    (hBn : ∀ i N k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B i N k)‖ ≤ K i)
    (X : ∀ N : ℕ, Ω → Group (Fin N))
    (hX : ∀ N, MeasurePreserving (X N) μ (haar (Fin N))) :
    ∀ᵐ ω ∂μ, ∀ i, Tendsto (fun N => traceWord (A i N) (B i N) (X N ω)) atTop (𝓝 0) := by
  exact ae_all_iff.mpr (fun i => ae_centered_traceWord_tendsto μ (hr i) (K i) (hK i)
    (A i) (B i) (hA i) (hB i) (hAn i) (hBn i) X hX)

end FreeProbability.Orthogonal

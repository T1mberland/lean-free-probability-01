import FreeProbability.RandomMatrix.OrthogonalMultiTraceProbabilityRandomInputsBounds
import Mathlib.MeasureTheory.Integral.Prod

/-! # Actual product-law second moments for random matrix inputs -/

noncomputable section
open scoped Classical Topology
namespace FreeProbability.Orthogonal
open Matrix MeasureTheory Filter
variable {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ) [IsProbabilityMeasure ν]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The actual product-law observable, with independently sampled input data
and an actual orthogonal Haar matrix. -/
def randomInputsTraceWord {r : ℕ} (A B : Θ → Fin r → Matrix n n ℂ)
    (z : Θ × Group n) : ℂ := traceWord (A z.1) (B z.1) z.2

/-- Genuine squared-norm product-law integral. -/
def randomInputsTraceWordSecondMoment {r : ℕ} (A B : Θ → Fin r → Matrix n n ℂ) : ℝ :=
  ∫ z : Θ × Group n, ‖randomInputsTraceWord A B z‖ ^ 2 ∂ν.prod (haar n)

/-- Measurability and actual almost-everywhere operator bounds suffice for
integrability of the squared observable; integrability is not a premise. -/
theorem integrable_randomInputsTraceWord_norm_sq {r : ℕ} (hr : 0 < r) (K : ℝ) (hK : 0 ≤ K)
    (A B : Θ → Fin r → Matrix n n ℂ) (hAm : Measurable A) (hBm : Measurable B)
    (hAn : ∀ᵐ θ ∂ν, ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A θ k)‖ ≤ K)
    (hBn : ∀ᵐ θ ∂ν, ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B θ k)‖ ≤ K) :
    Integrable (fun z : Θ × Group n => ‖randomInputsTraceWord A B z‖ ^ 2) (ν.prod (haar n)) := by
  have hm : Measurable (randomInputsTraceWord A B) :=
    measurable_traceWord_inputs (Ω := Θ × Group n) (n := n) (r := r) (fun z => A z.1) (fun z => B z.1) Prod.snd
      (hAm.comp measurable_fst) (hBm.comp measurable_fst) measurable_snd
  apply Integrable.of_bound (hm.norm.pow_const 2).aestronglyMeasurable ((K ^ (2 * r)) ^ 2)
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := ν) (ν := haar n)).ae hAn, (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := haar n)).ae hBn] with z hzA hzB
  simp only [Real.norm_eq_abs, abs_sq]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
    (traceWord_norm_le_uniform hr K hK (A z.1) (B z.1) z.2 hzA hzB)

/-- Actual Fubini identifies the product second moment with the average of
the genuine Haar second moments for the sampled deterministic inputs. -/
theorem randomInputsTraceWordSecondMoment_eq_integral {r : ℕ} (hr : 0 < r) (K : ℝ) (hK : 0 ≤ K)
    (A B : Θ → Fin r → Matrix n n ℂ) (hAm : Measurable A) (hBm : Measurable B)
    (hAn : ∀ᵐ θ ∂ν, ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A θ k)‖ ≤ K)
    (hBn : ∀ᵐ θ ∂ν, ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B θ k)‖ ≤ K) :
    randomInputsTraceWordSecondMoment ν A B = ∫ θ, traceWordSecondMoment (A θ) (B θ) ∂ν := by
  exact integral_prod _ (integrable_randomInputsTraceWord_norm_sq ν hr K hK A B hAm hBm hAn hBn)

/-- The actual uniform Haar estimate integrates against arbitrary independent
input data, with only measurable, almost-everywhere centered bounded factors. -/
theorem eventually_randomInputs_traceWordSecondMoment_bound {r : ℕ}
    (hr : 0 < r) (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ N : ℕ in atTop, ∀ (A B : Θ → Fin r → Matrix (Fin N) (Fin N) ℂ),
      Measurable A → Measurable B →
      (∀ᵐ θ ∂ν, ∀ k, Matrix.trace (A θ k) = 0) →
      (∀ᵐ θ ∂ν, ∀ k, Matrix.trace (B θ k) = 0) →
      (∀ᵐ θ ∂ν, ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A θ k)‖ ≤ K) →
      (∀ᵐ θ ∂ν, ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B θ k)‖ ≤ K) →
      randomInputsTraceWordSecondMoment ν A B ≤
        orthogonalCenteredTraceConstant (r + r) * K ^ (2 * (r + r)) * ((N : ℝ)⁻¹) ^ 2 := by
  filter_upwards [eventually_centered_traceWordSecondMoment_bound hr K hK] with N hN
  intro A B hAm hBm hA hB hAn hBn
  have hi := integrable_randomInputsTraceWord_norm_sq ν hr K hK A B hAm hBm hAn hBn
  rw [randomInputsTraceWordSecondMoment_eq_integral ν hr K hK A B hAm hBm hAn hBn]
  have hb : ∀ᵐ θ ∂ν, traceWordSecondMoment (A θ) (B θ) ≤
      orthogonalCenteredTraceConstant (r + r) * K ^ (2 * (r + r)) * ((N : ℝ)⁻¹) ^ 2 := by
    filter_upwards [hA, hB, hAn, hBn] with θ hcA hcB hnA hnB
    exact hN (A θ) (B θ) hcA hcB hnA hnB
  simpa only [randomInputsTraceWord, traceWordSecondMoment, integral_const, Measure.real,
    measure_univ, ENNReal.toReal_one, one_smul] using
    integral_mono_ae hi.integral_prod_left (integrable_const _) hb

end FreeProbability.Orthogonal

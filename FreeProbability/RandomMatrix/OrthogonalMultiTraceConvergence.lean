import FreeProbability.RandomMatrix.OrthogonalMultiTraceSecondMoment
import Mathlib.Analysis.PSeries

/-! # Genuine mean square convergence of centered Haar trace words -/

noncomputable section
open scoped Classical Topology
namespace FreeProbability.Orthogonal
open Matrix MeasureTheory Filter
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Actual squared trace norms are genuinely Haar integrable. -/
theorem integrable_traceWord_norm_sq {r : ℕ} (hr : 0 < r)
    (A B : Fin r → Matrix n n ℂ) :
    Integrable (fun U : Group n => ‖traceWord A B U‖ ^ 2) (haar n) := by
  convert (integrable_twoTraceWord hr hr A B
    (fun k => entrywiseConjugateMatrix (A k))
    (fun k => entrywiseConjugateMatrix (B k))).norm using 1
  funext U
  rw [← traceWord_conjugate, norm_mul]
  change ‖traceWord A B U‖ ^ 2 = ‖traceWord A B U‖ * ‖star (traceWord A B U)‖
  rw [norm_star, pow_two]

/-- Uniformly operator-bounded centered deterministic words converge to zero
in their actual Haar second absolute moments. -/
theorem tendsto_centered_traceWordSecondMoment {r : ℕ} (hr : 0 < r) (K : ℝ) (hK : 0 ≤ K)
    (A B : ∀ N : ℕ, Fin r → Matrix (Fin N) (Fin N) ℂ)
    (hA : ∀ N k, Matrix.trace (A N k) = 0) (hB : ∀ N k, Matrix.trace (B N k) = 0)
    (hAn : ∀ N k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A N k)‖ ≤ K)
    (hBn : ∀ N k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B N k)‖ ≤ K) :
    Tendsto (fun N => traceWordSecondMoment (A N) (B N)) atTop (𝓝 0) := by
  have hb : ∀ᶠ N : ℕ in atTop, traceWordSecondMoment (A N) (B N) ≤
      orthogonalCenteredTraceConstant (r + r) * K ^ (2 * (r + r)) * ((N : ℝ)⁻¹) ^ 2 := by
    filter_upwards [eventually_centered_traceWordSecondMoment_bound hr K hK] with N hN
    exact hN (A N) (B N) (hA N) (hB N) (hAn N) (hBn N)
  apply squeeze_zero' (Filter.Eventually.of_forall (fun N => traceWordSecondMoment_nonneg _ _)) hb
  have hi : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero] using
    tendsto_const_nhds.mul
      (f := fun _ : ℕ => orthogonalCenteredTraceConstant (r + r) * K ^ (2 * (r + r))) (hi.pow 2)

/-- The actual second absolute moments are summable over all matrix dimensions,
including the finitely many dimensions below the stable pairing threshold. -/
theorem summable_centered_traceWordSecondMoment {r : ℕ} (hr : 0 < r) (K : ℝ) (hK : 0 ≤ K)
    (A B : ∀ N : ℕ, Fin r → Matrix (Fin N) (Fin N) ℂ)
    (hA : ∀ N k, Matrix.trace (A N k) = 0) (hB : ∀ N k, Matrix.trace (B N k) = 0)
    (hAn : ∀ N k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A N k)‖ ≤ K)
    (hBn : ∀ N k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B N k)‖ ≤ K) :
    Summable (fun N => traceWordSecondMoment (A N) (B N)) := by
  have hs : Summable (fun N : ℕ => ((N : ℝ)⁻¹) ^ 2) := by
    simpa only [inv_pow] using (Real.summable_nat_pow_inv.mpr (by decide : 1 < (2 : ℕ)))
  apply (hs.mul_left (orthogonalCenteredTraceConstant (r + r) * K ^ (2 * (r + r)))).of_norm_bounded_eventually_nat
  filter_upwards [eventually_centered_traceWordSecondMoment_bound hr K hK] with N hN
  simpa only [Real.norm_eq_abs, abs_of_nonneg (traceWordSecondMoment_nonneg _ _)] using
    hN (A N) (B N) (hA N) (hB N) (hAn N) (hBn N)

end FreeProbability.Orthogonal

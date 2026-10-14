import FreeProbability.RandomMatrix.OrthogonalColoredTraceRunData

/-! # Actual selected-Haar word restoration after centering runs -/

noncomputable section
open scoped Classical Topology
namespace FreeProbability.Orthogonal
open Matrix Filter

/-- Centering finitely many right-run factors whose ACTUAL normalized traces
vanish changes the selected-Haar trace word by a quantity tending to zero.
The orthogonal matrix may vary arbitrarily with dimension. -/
theorem tendsto_traceWord_right_center_sub {r : ℕ} (K : ℝ) (hK : 0 ≤ K)
    (A B : ∀ N : ℕ, Fin r → Matrix (Fin N) (Fin N) ℂ)
    (U : ∀ N : ℕ, Group (Fin N))
    (hA : ∀ N k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A N k)‖ ≤ K)
    (hB : ∀ N k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B N k)‖ ≤ K)
    (ht : ∀ k, Tendsto (fun N => normalizedTrace (B N k)) atTop (𝓝 0)) :
    Tendsto (fun N => traceWord (A N) (B N) (U N) -
      traceWord (A N) (fun k => matrixTraceCenter (B N k)) (U N)) atTop (𝓝 0) := by
  let C := fun N k => complexMatrix (U N) * A N k * (complexMatrix (U N)).transpose * B N k
  let D := fun N k => complexMatrix (U N) * A N k * (complexMatrix (U N)).transpose * matrixTraceCenter (B N k)
  apply tendsto_normalizedTrace_orderedProduct_sub (2 * K ^ 2) (by positivity) C D
  · intro N k
    have hb := traceWord_block_opNorm_le (U N) (A N k) (B N k)
    have hc := mul_le_mul (hA N k) (hB N k) (norm_nonneg _) hK
    exact hb.trans (hc.trans (by nlinarith [sq_nonneg K]))
  · intro N k
    have hb := traceWord_block_opNorm_le (U N) (A N k) (matrixTraceCenter (B N k))
    have hbc := (matrixTraceCenter_opNorm_le (B N k)).trans
      (mul_le_mul_of_nonneg_left (hB N k) (by positivity))
    have hc := mul_le_mul (hA N k) hbc (norm_nonneg _) hK
    exact hb.trans (hc.trans (by ring_nf; exact le_refl _))
  · intro k
    have hd : ∀ᶠ N : ℕ in atTop, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (C N k - D N k)‖ ≤
        K * ‖normalizedTrace (B N k)‖ := by
      filter_upwards with N
      have he : C N k - D N k = complexMatrix (U N) * A N k * (complexMatrix (U N)).transpose *
          (B N k - matrixTraceCenter (B N k)) := by
        dsimp only [C, D]
        rw [mul_sub]
      rw [he]
      exact (traceWord_block_opNorm_le (U N) _ _).trans
        (mul_le_mul (hA N k) (sub_matrixTraceCenter_opNorm_le (B N k)) (norm_nonneg _) hK)
    apply squeeze_zero' (Eventually.of_forall (fun N => norm_nonneg _)) hd
    have hn := tendsto_zero_iff_norm_tendsto_zero.mp (ht k)
    simpa only [mul_zero] using tendsto_const_nhds.mul (f := fun _ : ℕ => K) hn

end FreeProbability.Orthogonal

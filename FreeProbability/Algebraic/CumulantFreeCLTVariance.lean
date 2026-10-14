import FreeProbability.Algebraic.CumulantFreeCLT
import FreeProbability.Algebraic.CumulantLowOrder

/-! # Free central limit moments in terms of the actual marginal variance -/

namespace FreeProbability

open Filter Topology

variable {E : Type*} [Ring E] [Algebra ℝ E]

/-- The pairing moment limit uses the actual second moment of the centered marginal. -/
theorem freeCLT_pairingMoments_variance {D : ℕ → Type*} [∀ N, Ring (D N)] [∀ N, Algebra ℝ (D N)]
    (φN : ∀ N, ProbabilitySpace ℝ (D N)) (B : ∀ N, Fin N → Subalgebra ℝ (D N))
    (aN : ∀ N, Fin N → D N) (ψ : ProbabilitySpace ℝ E) (b : E)
    (hfree : ∀ N, FreelyIndependent (φN N) (B N))
    (hmem : ∀ N i, aN N i ∈ B N i)
    (hmarg : ∀ N i k, (φN N).expectation (aN N i ^ k) = ψ.expectation (b ^ k))
    (hcenter : ψ.expectation b = 0) (k : ℕ) :
    Tendsto (fun N => (φN N).expectation
      (((Real.sqrt (N : ℝ))⁻¹ • ∑ i, aN N i) ^ k)) atTop
      (𝓝 ((Fintype.card (NoncrossingPairing k) : ℝ) * ψ.expectation (b ^ 2) ^ (k / 2))) := by
  simpa only [cumulant_pair_self_of_centered ψ b hcenter] using
    freeCLT_pairingMoments φN B aN ψ b hfree hmem hmarg hcenter k

/-- At unit variance, every normalized iid free-sum moment tends to the pairing count. -/
theorem freeCLT_pairingMoments_variance_one {D : ℕ → Type*} [∀ N, Ring (D N)] [∀ N, Algebra ℝ (D N)]
    (φN : ∀ N, ProbabilitySpace ℝ (D N)) (B : ∀ N, Fin N → Subalgebra ℝ (D N))
    (aN : ∀ N, Fin N → D N) (ψ : ProbabilitySpace ℝ E) (b : E)
    (hfree : ∀ N, FreelyIndependent (φN N) (B N))
    (hmem : ∀ N i, aN N i ∈ B N i)
    (hmarg : ∀ N i k, (φN N).expectation (aN N i ^ k) = ψ.expectation (b ^ k))
    (hcenter : ψ.expectation b = 0) (hvariance : ψ.expectation (b ^ 2) = 1) (k : ℕ) :
    Tendsto (fun N => (φN N).expectation
      (((Real.sqrt (N : ℝ))⁻¹ • ∑ i, aN N i) ^ k)) atTop
      (𝓝 (Fintype.card (NoncrossingPairing k) : ℝ)) := by
  simpa only [hvariance, one_pow, mul_one] using
    freeCLT_pairingMoments_variance φN B aN ψ b hfree hmem hmarg hcenter k

end FreeProbability

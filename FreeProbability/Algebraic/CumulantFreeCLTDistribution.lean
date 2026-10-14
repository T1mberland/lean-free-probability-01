import FreeProbability.Algebraic.CumulantRCLikeFreeCLT
import FreeProbability.Algebraic.MomentConvergence
import Mathlib.Algebra.Star.BigOperators

/-!
# Polynomial and star-moment free central limit convergence

The explicit pairing moment limit implies convergence in the library's algebraic
polynomial-distribution interface to any semicircular-cumulant realization. For
self-adjoint summands and limit, it also implies convergence against all star
polynomials. These are algebraic moment statements, not spectral inclusion.
-/

namespace FreeProbability

open Filter Topology

variable {𝕜 E A : Type*} [RCLike 𝕜] [Ring E] [Algebra 𝕜 E] [Ring A] [Algebra 𝕜 A]

/-- Normalized iid free sums converge against every polynomial in one variable. -/
theorem freeCLT_convergesInDistribution {D : ℕ → Type*}
    [∀ N, Ring (D N)] [∀ N, Algebra 𝕜 (D N)]
    (φN : ∀ N, ProbabilitySpace 𝕜 (D N)) (B : ∀ N, Fin N → Subalgebra 𝕜 (D N))
    (aN : ∀ N, Fin N → D N) (ψ : ProbabilitySpace 𝕜 E) (b : E)
    (φ : ProbabilitySpace 𝕜 A) (s : A)
    (hfree : ∀ N, FreelyIndependent (φN N) (B N))
    (hmem : ∀ N i, aN N i ∈ B N i)
    (hmarg : ∀ N i k, (φN N).expectation (aN N i ^ k) = ψ.expectation (b ^ k))
    (hcenter : ψ.expectation b = 0)
    (hs : HasSemicircularCumulants φ s (ψ.expectation (b ^ 2))) :
    ConvergesInDistribution φN
      (fun N (_ : Unit) => ((Real.sqrt (N : ℝ))⁻¹ : 𝕜) • ∑ i, aN N i)
      φ (fun _ : Unit => s) atTop := by
  apply (convergesInDistribution_iff_moments _ _ _ _ _).mpr
  intro w
  have h := freeCLT_pairingMoments_rclike φN B aN ψ b hfree hmem hmarg hcenter w.length
  rw [← hs.expectation_pow] at h
  simpa only [jointMoment, List.map_const', List.prod_replicate] using h

/-- For a self-adjoint sequence and limit, power-moment convergence implies all star-polynomial convergence. -/
theorem convergesInStarDistribution_of_selfAdjoint_powerMoments {D : ℕ → Type*}
    [Star A] [∀ N, Ring (D N)] [∀ N, Algebra 𝕜 (D N)] [∀ N, Star (D N)]
    (φN : ∀ N, ProbabilitySpace 𝕜 (D N)) (aN : ∀ N, D N) (φ : ProbabilitySpace 𝕜 A) (s : A)
    (hsource : ∀ N, star (aN N) = aN N) (htarget : star s = s)
    (hpow : ∀ k, Tendsto (fun N => (φN N).expectation (aN N ^ k)) atTop (𝓝 (φ.expectation (s ^ k)))) :
    ConvergesInStarDistribution φN (fun N (_ : Unit) => aN N) φ (fun _ : Unit => s) atTop := by
  have hsf (N : ℕ) : starFamily (fun _ : Unit => aN N) = (fun _ : Unit × Bool => aN N) := by
    funext p
    rcases p with ⟨u, p⟩
    cases p <;> simp [starFamily, hsource]
  have htf : starFamily (fun _ : Unit => s) = (fun _ : Unit × Bool => s) := by
    funext p
    rcases p with ⟨u, p⟩
    cases p <;> simp [starFamily, htarget]
  unfold ConvergesInStarDistribution
  apply (convergesInDistribution_iff_moments _ _ _ _ _).mpr
  intro w
  simpa only [hsf, htf, jointMoment, List.map_const', List.prod_replicate] using hpow w.length

/-- The free central limit theorem against all star polynomials for self-adjoint summands. -/
theorem freeCLT_convergesInStarDistribution {D : ℕ → Type*}
    [StarRing A] [∀ N, Ring (D N)] [∀ N, Algebra 𝕜 (D N)] [∀ N, StarRing (D N)]
    [∀ N, StarModule 𝕜 (D N)]
    (φN : ∀ N, ProbabilitySpace 𝕜 (D N)) (B : ∀ N, Fin N → Subalgebra 𝕜 (D N))
    (aN : ∀ N, Fin N → D N) (ψ : ProbabilitySpace 𝕜 E) (b : E)
    (φ : ProbabilitySpace 𝕜 A) (s : A)
    (hfree : ∀ N, FreelyIndependent (φN N) (B N))
    (hmem : ∀ N i, aN N i ∈ B N i)
    (hmarg : ∀ N i k, (φN N).expectation (aN N i ^ k) = ψ.expectation (b ^ k))
    (hcenter : ψ.expectation b = 0)
    (hs : HasSemicircularCumulants φ s (ψ.expectation (b ^ 2)))
    (hstars : ∀ N i, star (aN N i) = aN N i) (hstar : star s = s) :
    ConvergesInStarDistribution φN
      (fun N (_ : Unit) => ((Real.sqrt (N : ℝ))⁻¹ : 𝕜) • ∑ i, aN N i)
      φ (fun _ : Unit => s) atTop := by
  apply convergesInStarDistribution_of_selfAdjoint_powerMoments
  · intro N
    simp [star_smul, star_sum, hstars]
  · exact hstar
  · intro k
    have h := freeCLT_pairingMoments_rclike φN B aN ψ b hfree hmem hmarg hcenter k
    rw [← hs.expectation_pow] at h
    exact h

end FreeProbability

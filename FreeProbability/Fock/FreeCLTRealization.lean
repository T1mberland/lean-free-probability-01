import FreeProbability.Fock.CumulantLaw
import FreeProbability.Algebraic.CumulantFreeCLTDistribution

/-!
# The variance-one free CLT with a concrete faithful tracial target

Centered iid free triangular arrays converge in polynomial moments to the actual
Fock generator. Self-adjoint arrays converge against all star polynomials.
Neither a limiting realization nor its cumulant law is assumed; no spectral or
operator-norm convergence is claimed.
-/

namespace FreeProbability.Fock

variable {E : Type*} [Ring E] [Algebra ℂ E]

/-- Polynomial free CLT with an actual constructed semicircular target. -/
theorem freeCLT_convergesTo_closedSemicircular {D : ℕ → Type*}
    [∀ N, Ring (D N)] [∀ N, Algebra ℂ (D N)]
    (φN : ∀ N, ProbabilitySpace ℂ (D N)) (B : ∀ N, Fin N → Subalgebra ℂ (D N))
    (aN : ∀ N, Fin N → D N) (ψ : ProbabilitySpace ℂ E) (b : E)
    (hfree : ∀ N, FreelyIndependent (φN N) (B N))
    (hmem : ∀ N i, aN N i ∈ B N i)
    (hmarg : ∀ N i k, (φN N).expectation (aN N i ^ k) = ψ.expectation (b ^ k))
    (hcenter : ψ.expectation b = 0) (hvariance : ψ.expectation (b ^ 2) = 1) :
    ConvergesInDistribution φN
      (fun N (_ : Unit) => ((Real.sqrt (N : ℝ))⁻¹ : ℂ) • ∑ i, aN N i)
      (closedGeneratedVacuumState Unit).toProbabilitySpace
      (fun _ : Unit => closedSemicircular ()) Filter.atTop := by
  apply freeCLT_convergesInDistribution φN B aN ψ b
    (closedGeneratedVacuumState Unit).toProbabilitySpace (closedSemicircular ())
    hfree hmem hmarg hcenter
  rw [hvariance]
  exact closedSemicircular_hasSemicircularCumulants ()

/-- Star-polynomial free CLT for self-adjoint arrays with an actual constructed target. -/
theorem freeCLT_convergesInStarDistribution_closedSemicircular {D : ℕ → Type*}
    [∀ N, Ring (D N)] [∀ N, Algebra ℂ (D N)] [∀ N, StarRing (D N)]
    [∀ N, StarModule ℂ (D N)]
    (φN : ∀ N, ProbabilitySpace ℂ (D N)) (B : ∀ N, Fin N → Subalgebra ℂ (D N))
    (aN : ∀ N, Fin N → D N) (ψ : ProbabilitySpace ℂ E) (b : E)
    (hfree : ∀ N, FreelyIndependent (φN N) (B N))
    (hmem : ∀ N i, aN N i ∈ B N i)
    (hmarg : ∀ N i k, (φN N).expectation (aN N i ^ k) = ψ.expectation (b ^ k))
    (hcenter : ψ.expectation b = 0) (hvariance : ψ.expectation (b ^ 2) = 1)
    (hstars : ∀ N i, star (aN N i) = aN N i) :
    ConvergesInStarDistribution φN
      (fun N (_ : Unit) => ((Real.sqrt (N : ℝ))⁻¹ : ℂ) • ∑ i, aN N i)
      (closedGeneratedVacuumState Unit).toProbabilitySpace
      (fun _ : Unit => closedSemicircular ()) Filter.atTop := by
  apply freeCLT_convergesInStarDistribution φN B aN ψ b
    (closedGeneratedVacuumState Unit).toProbabilitySpace (closedSemicircular ())
    hfree hmem hmarg hcenter _ hstars
    (isSelfAdjoint_closedSemicircular ()).star_eq
  rw [hvariance]
  exact closedSemicircular_hasSemicircularCumulants ()

end FreeProbability.Fock

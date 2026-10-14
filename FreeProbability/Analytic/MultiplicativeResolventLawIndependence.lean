import FreeProbability.Analytic.MultiplicativeResolventLaw
import FreeProbability.Algebraic.DistributionComparison
import Mathlib.Tactic.FinCases

/-! # Actual positive multiplicative laws depend only on the marginal laws -/

noncomputable section
open MeasureTheory
namespace FreeProbability

private def pairFamily {A : Type*} (a b : A) (i : Fin 2) : A := if i = 0 then a else b

section Algebraic
variable {𝕜 A D : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A] [Ring D] [Algebra 𝕜 D]

/-- Ordered product moments of two given free pairs agree across different
ambient algebras whenever the marginal power moments agree. -/
theorem expectation_pow_product_eq_of_free_marginal_moments
    (φ : ProbabilitySpace 𝕜 A) (ψ : ProbabilitySpace 𝕜 D)
    {B : Fin 2 → Subalgebra 𝕜 A} {C : Fin 2 → Subalgebra 𝕜 D}
    (hf : FreelyIndependent φ B) (hg : FreelyIndependent ψ C)
    (a b : A) (c d : D) (ha : a ∈ B 0) (hb : b ∈ B 1) (hc : c ∈ C 0) (hd : d ∈ C 1)
    (hmac : ∀ n : ℕ, φ.expectation (a ^ n) = ψ.expectation (c ^ n))
    (hmbd : ∀ n : ℕ, φ.expectation (b ^ n) = ψ.expectation (d ^ n)) (n : ℕ) :
    φ.expectation ((a * b) ^ n) = ψ.expectation ((c * d) ^ n) := by
  have hAmem (i : Fin 2) : pairFamily a b i ∈ B i := by
    fin_cases i
    · simpa [pairFamily] using ha
    · simpa [pairFamily] using hb
  have hDmem (i : Fin 2) : pairFamily c d i ∈ C i := by
    fin_cases i
    · simpa [pairFamily] using hc
    · simpa [pairFamily] using hd
  have hfa : FreelyIndependent φ (fun i => Algebra.adjoin 𝕜 {pairFamily a b i}) :=
    hf.mono (fun i => Algebra.adjoin_le (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hAmem i))
  have hgd : FreelyIndependent ψ (fun i => Algebra.adjoin 𝕜 {pairFamily c d i}) :=
    hg.mono (fun i => Algebra.adjoin_le (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hDmem i))
  have hmarg (i : Fin 2) (k : ℕ) : φ.expectation (pairFamily a b i ^ k) =
      ψ.expectation (pairFamily c d i ^ k) := by
    fin_cases i
    · simpa [pairFamily] using hmac k
    · simpa [pairFamily] using hmbd k
  have h := sameDistribution_of_free_marginals φ ψ _ _ hfa hgd hmarg
    ((List.replicate n [(0 : Fin 2), 1]).flatten)
  simpa [jointMoment, pairFamily, List.map_flatten, List.map_replicate, List.prod_flatten] using h
end Algebraic

variable {A D : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

/-- The actual positive multiplication probability law is independent of the
chosen bounded free-pair realization when its marginal moments agree. No
nonzero first-moment or faithful-state hypothesis is required. -/
theorem positiveMultiplicativeProbabilityLaw_eq_of_marginal_moments
    (φ : StarProbabilitySpace A) (ψ : StarProbabilitySpace D)
    (hφ : IsTracial φ.toProbabilitySpace) (hψ : IsTracial ψ.toProbabilitySpace)
    {B : Fin 2 → Subalgebra ℂ A} {C : Fin 2 → Subalgebra ℂ D}
    (hf : FreelyIndependent φ.toProbabilitySpace B) (hg : FreelyIndependent ψ.toProbabilitySpace C)
    (a b : A) (c d : D) (ha : a ∈ B 0) (hb : b ∈ B 1) (hc : c ∈ C 0) (hd : d ∈ C 1)
    (hapos : 0 ≤ a) (hbpos : 0 ≤ b) (hcpos : 0 ≤ c) (hdpos : 0 ≤ d)
    (hmac : ∀ n : ℕ, φ.expectation (a ^ n) = ψ.expectation (c ^ n))
    (hmbd : ∀ n : ℕ, φ.expectation (b ^ n) = ψ.expectation (d ^ n)) :
    positiveMultiplicativeProbabilityLaw φ a b hbpos = positiveMultiplicativeProbabilityLaw ψ c d hdpos := by
  apply Subtype.ext
  apply spectralMeasure_eq_of_power_moments
  intro n
  rw [φ.expectation_pow_positiveMultiplicativeSandwich hφ a b hapos,
    ψ.expectation_pow_positiveMultiplicativeSandwich hψ c d hcpos]
  exact expectation_pow_product_eq_of_free_marginal_moments φ.toProbabilitySpace ψ.toProbabilitySpace
    hf hg a b c d ha hb hc hd hmac hmbd n

/-- Equality of the genuine marginal spectral probability measures determines
exactly the same actual positive product law in any other free realization. -/
theorem positiveMultiplicativeProbabilityLaw_eq_of_marginal_laws
    (φ : StarProbabilitySpace A) (ψ : StarProbabilitySpace D)
    (hφ : IsTracial φ.toProbabilitySpace) (hψ : IsTracial ψ.toProbabilitySpace)
    {B : Fin 2 → Subalgebra ℂ A} {C : Fin 2 → Subalgebra ℂ D}
    (hf : FreelyIndependent φ.toProbabilitySpace B) (hg : FreelyIndependent ψ.toProbabilitySpace C)
    (a b : A) (c d : D) (ha : a ∈ B 0) (hb : b ∈ B 1) (hc : c ∈ C 0) (hd : d ∈ C 1)
    (hapos : 0 ≤ a) (hbpos : 0 ≤ b) (hcpos : 0 ≤ c) (hdpos : 0 ≤ d)
    (hmac : spectralProbabilityMeasure φ hapos.isSelfAdjoint = spectralProbabilityMeasure ψ hcpos.isSelfAdjoint)
    (hmbd : spectralProbabilityMeasure φ hbpos.isSelfAdjoint = spectralProbabilityMeasure ψ hdpos.isSelfAdjoint) :
    positiveMultiplicativeProbabilityLaw φ a b hbpos = positiveMultiplicativeProbabilityLaw ψ c d hdpos := by
  apply positiveMultiplicativeProbabilityLaw_eq_of_marginal_moments φ ψ hφ hψ hf hg a b c d ha hb hc hd
    hapos hbpos hcpos hdpos
  · exact (spectralMeasure_eq_iff_power_moments φ ψ hapos.isSelfAdjoint hcpos.isSelfAdjoint).mp
      (congrArg (fun μ : ProbabilityMeasure ℝ => (μ : Measure ℝ)) hmac)
  · exact (spectralMeasure_eq_iff_power_moments φ ψ hbpos.isSelfAdjoint hdpos.isSelfAdjoint).mp
      (congrArg (fun μ : ProbabilityMeasure ℝ => (μ : Measure ℝ)) hmbd)
end FreeProbability

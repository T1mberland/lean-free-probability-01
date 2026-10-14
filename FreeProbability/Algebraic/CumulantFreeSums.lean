import FreeProbability.Algebraic.FormalRTransform
import FreeProbability.Algebraic.UnivariateCumulant

/-!
# Exact cumulants of scaled identically distributed free sums

The hypotheses use equal actual power moments, rather than assuming equality of
cumulants. This finite identity is the coefficient calculation for the free
central limit theorem, with no positivity or analytic assumptions.
-/

namespace FreeProbability

variable {𝕜 A E I : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A] [Ring E] [Algebra 𝕜 E] [Fintype I]

/-- Exact univariate cumulants of a scaled sum of a finite identically distributed free family. -/
theorem FreelyIndependent.cumulant_replicate_scaled_sum {φ : ProbabilitySpace 𝕜 A}
    {B : I → Subalgebra 𝕜 A} (hfree : FreelyIndependent φ B)
    (a : I → A) (ha : ∀ i, a i ∈ B i) (ψ : ProbabilitySpace 𝕜 E) (b : E)
    (hmarg : ∀ i n, φ.expectation (a i ^ n) = ψ.expectation (b ^ n)) (c : 𝕜) (n : ℕ) :
    cumulant φ (List.replicate n (c • ∑ i, a i)) =
      c ^ n * (Fintype.card I : 𝕜) * cumulant ψ (List.replicate n b) := by
  classical
  rw [cumulant_replicate_smul, hfree.cumulant_replicate_sum a ha]
  have hc (i : I) : cumulant φ (List.replicate n (a i)) = cumulant ψ (List.replicate n b) :=
    cumulant_replicate_eq_of_powerMoments φ ψ (a i) b (hmarg i) n
  simp only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

/-- The first cumulant of a sum of centered free copies remains zero at any scale. -/
theorem FreelyIndependent.cumulant_one_scaled_sum {φ : ProbabilitySpace 𝕜 A}
    {B : I → Subalgebra 𝕜 A} (hfree : FreelyIndependent φ B)
    (a : I → A) (ha : ∀ i, a i ∈ B i) (ψ : ProbabilitySpace 𝕜 E) (b : E)
    (hmarg : ∀ i n, φ.expectation (a i ^ n) = ψ.expectation (b ^ n))
    (hcenter : ψ.expectation b = 0) (c : 𝕜) :
    cumulant φ [c • ∑ i, a i] = 0 := by
  have h := hfree.cumulant_replicate_scaled_sum a ha ψ b hmarg c 1
  simpa [cumulant, freeCumulant_singleton, hcenter] using h

end FreeProbability

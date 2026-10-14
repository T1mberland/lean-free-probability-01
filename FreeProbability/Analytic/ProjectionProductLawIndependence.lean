import FreeProbability.Analytic.ProjectionProductLaw
import FreeProbability.Analytic.MultiplicativeResolventLawIndependence

/-! # Actual finite positive-product laws depend only on marginal laws -/

noncomputable section
open MeasureTheory
namespace FreeProbability
variable {A D : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

private def boolPairIndex (i : Fin 2) : Bool := if i = 0 then false else true
private theorem boolPairIndex_injective : Function.Injective boolPairIndex := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [boolPairIndex]

/-- All power moments of actual finite positive products agree across
different ambient algebras when the free marginal power moments agree. -/
theorem expectation_pow_iteratedPositiveProduct_eq_of_free_marginals
    (φ : StarProbabilitySpace A) (ψ : StarProbabilitySpace D)
    (hφ : IsTracial φ.toProbabilitySpace) (hψ : IsTracial ψ.toProbabilitySpace)
    (n : ℕ) {B : Fin n → Subalgebra ℂ A} {C : Fin n → Subalgebra ℂ D}
    (hf : FreelyIndependent φ.toProbabilitySpace B) (hg : FreelyIndependent ψ.toProbabilitySpace C)
    (p : Fin n → A) (q : Fin n → D) (hpB : ∀ i, p i ∈ B i) (hqC : ∀ i, q i ∈ C i)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hmarg : ∀ i k, φ.expectation (p i ^ k) = ψ.expectation (q i ^ k)) (k : ℕ) :
    φ.expectation (iteratedPositiveProduct n p ^ k) =
      ψ.expectation (iteratedPositiveProduct n q ^ k) := by
  induction n generalizing k with
  | zero => simp [iteratedPositiveProduct, φ.toProbabilitySpace.expectation_one,
      ψ.toProbabilitySpace.expectation_one]
  | succ n ih =>
    have hfp := φ.freelyIndependent_closedStarGrouped hf p hpB
      (fun i => (hp i).isSelfAdjoint) (prefixLastGroup n)
    have hgq := ψ.freelyIndependent_closedStarGrouped hg q hqC
      (fun i => (hq i).isSelfAdjoint) (prefixLastGroup n)
    have hfa := hfp.reindex boolPairIndex boolPairIndex_injective
    have hga := hgq.reindex boolPairIndex boolPairIndex_injective
    change φ.expectation (positiveMultiplicativeSandwich _ _ ^ k) =
      ψ.expectation (positiveMultiplicativeSandwich _ _ ^ k)
    rw [φ.expectation_pow_positiveMultiplicativeSandwich hφ _ _
        (iteratedPositiveProduct_nonneg n _ (fun i => hp i.castSucc)),
      ψ.expectation_pow_positiveMultiplicativeSandwich hψ _ _
        (iteratedPositiveProduct_nonneg n _ (fun i => hq i.castSucc))]
    apply expectation_pow_product_eq_of_free_marginal_moments φ.toProbabilitySpace ψ.toProbabilitySpace
      hfa hga
    · simpa [boolPairIndex] using iteratedPositiveProduct_mem_prefixGroup n p hp
    · simpa [boolPairIndex] using last_mem_prefixGroup n p
    · simpa [boolPairIndex] using iteratedPositiveProduct_mem_prefixGroup n q hq
    · simpa [boolPairIndex] using last_mem_prefixGroup n q
    · intro j
      exact ih (hf.reindex Fin.castSucc (Fin.castSucc_injective n))
        (hg.reindex Fin.castSucc (Fin.castSucc_injective n))
        (fun i => p i.castSucc) (fun i => q i.castSucc)
        (fun i => hpB i.castSucc) (fun i => hqC i.castSucc)
        (fun i => hp i.castSucc) (fun i => hq i.castSucc)
        (fun i => hmarg i.castSucc) j
    · exact hmarg (Fin.last n)

/-- The actual finite product probability law is independent of the supplied
free realization when its marginal power moments agree. Nonzero means and
faithfulness are not required. -/
theorem iteratedPositiveProbabilityLaw_eq_of_free_marginal_moments
    (φ : StarProbabilitySpace A) (ψ : StarProbabilitySpace D)
    (hφ : IsTracial φ.toProbabilitySpace) (hψ : IsTracial ψ.toProbabilitySpace)
    (n : ℕ) {B : Fin n → Subalgebra ℂ A} {C : Fin n → Subalgebra ℂ D}
    (hf : FreelyIndependent φ.toProbabilitySpace B) (hg : FreelyIndependent ψ.toProbabilitySpace C)
    (p : Fin n → A) (q : Fin n → D) (hpB : ∀ i, p i ∈ B i) (hqC : ∀ i, q i ∈ C i)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hmarg : ∀ i k, φ.expectation (p i ^ k) = ψ.expectation (q i ^ k)) :
    iteratedPositiveProbabilityLaw φ n p hp = iteratedPositiveProbabilityLaw ψ n q hq := by
  apply Subtype.ext
  apply spectralMeasure_eq_of_power_moments
  exact expectation_pow_iteratedPositiveProduct_eq_of_free_marginals φ ψ hφ hψ n hf hg p q
    hpB hqC hp hq hmarg

/-- Equal genuine marginal spectral measures determine equal actual finite
positive-product laws, even in different ambient algebras. -/
theorem iteratedPositiveProbabilityLaw_eq_of_free_marginal_laws
    (φ : StarProbabilitySpace A) (ψ : StarProbabilitySpace D)
    (hφ : IsTracial φ.toProbabilitySpace) (hψ : IsTracial ψ.toProbabilitySpace)
    (n : ℕ) {B : Fin n → Subalgebra ℂ A} {C : Fin n → Subalgebra ℂ D}
    (hf : FreelyIndependent φ.toProbabilitySpace B) (hg : FreelyIndependent ψ.toProbabilitySpace C)
    (p : Fin n → A) (q : Fin n → D) (hpB : ∀ i, p i ∈ B i) (hqC : ∀ i, q i ∈ C i)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hmarg : ∀ i, spectralProbabilityMeasure φ (hp i).isSelfAdjoint =
      spectralProbabilityMeasure ψ (hq i).isSelfAdjoint) :
    iteratedPositiveProbabilityLaw φ n p hp = iteratedPositiveProbabilityLaw ψ n q hq := by
  apply iteratedPositiveProbabilityLaw_eq_of_free_marginal_moments φ ψ hφ hψ n hf hg p q hpB hqC hp hq
  intro i
  exact (spectralMeasure_eq_iff_power_moments φ ψ (hp i).isSelfAdjoint (hq i).isSelfAdjoint).mp
    (congrArg (fun μ : ProbabilityMeasure ℝ => (μ : Measure ℝ)) (hmarg i))

/-- In particular the actual half-trace free-projection product law depends
only on the number of factors, without an assumed Bernoulli realization. -/
theorem iteratedHalfProjectionProbabilityLaw_eq
    (φ : StarProbabilitySpace A) (ψ : StarProbabilitySpace D)
    (hφ : IsTracial φ.toProbabilitySpace) (hψ : IsTracial ψ.toProbabilitySpace)
    (n : ℕ) {B : Fin n → Subalgebra ℂ A} {C : Fin n → Subalgebra ℂ D}
    (hf : FreelyIndependent φ.toProbabilitySpace B) (hg : FreelyIndependent ψ.toProbabilitySpace C)
    (p : Fin n → A) (q : Fin n → D) (hpB : ∀ i, p i ∈ B i) (hqC : ∀ i, q i ∈ C i)
    (hp : ∀ i, IsStarProjection (p i)) (hq : ∀ i, IsStarProjection (q i))
    (hEp : ∀ i, φ.expectation (p i) = (1 / 2 : ℂ))
    (hEq : ∀ i, ψ.expectation (q i) = (1 / 2 : ℂ)) :
    iteratedPositiveProbabilityLaw φ n p (fun i => (hp i).nonneg) =
      iteratedPositiveProbabilityLaw ψ n q (fun i => (hq i).nonneg) := by
  apply iteratedPositiveProbabilityLaw_eq_of_free_marginal_moments φ ψ hφ hψ n hf hg p q hpB hqC
    (fun i => (hp i).nonneg) (fun i => (hq i).nonneg)
  intro i k
  cases k with
  | zero => simp [φ.toProbabilitySpace.expectation_one, ψ.toProbabilitySpace.expectation_one]
  | succ k => rw [(hp i).pow_succ_eq, (hq i).pow_succ_eq, hEp i, hEq i]
end FreeProbability

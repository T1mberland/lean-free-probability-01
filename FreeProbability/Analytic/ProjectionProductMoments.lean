import FreeProbability.Analytic.ProjectionProductIteration
import Mathlib.Algebra.BigOperators.Fin

/-! # Actual finite free positive-product first moments -/

noncomputable section
open scoped BigOperators
namespace FreeProbability
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
namespace StarProbabilitySpace
variable (φ : FreeProbability.StarProbabilitySpace A)

/-- Each actual prefix and the next supplied factor are free through their
closed generated algebras, giving literal first-moment factorization. -/
theorem expectation_iteratedPositiveProduct_succ (hφ : IsTracial φ.toProbabilitySpace)
    (n : ℕ) {B : Fin (n + 1) → Subalgebra ℂ A}
    (hf : FreelyIndependent φ.toProbabilitySpace B) (p : Fin (n + 1) → A)
    (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, 0 ≤ p i) :
    φ.expectation (iteratedPositiveProduct (n + 1) p) =
      φ.expectation (iteratedPositiveProduct n (fun i => p i.castSucc)) *
        φ.expectation (p (Fin.last n)) := by
  have hg := φ.freelyIndependent_closedStarGrouped hf p hpB
    (fun i => (hp i).isSelfAdjoint) (prefixLastGroup n)
  have h := φ.expectation_pow_positiveMultiplicativeSandwich hφ
    (iteratedPositiveProduct n (fun i => p i.castSucc)) (p (Fin.last n))
    (iteratedPositiveProduct_nonneg n _ (fun i => hp i.castSucc)) 1
  simp only [pow_one] at h
  change φ.expectation (positiveMultiplicativeSandwich _ _) = _
  rw [h]
  exact hg.expectation_mul Bool.false_ne_true
    (iteratedPositiveProduct_mem_prefixGroup n p hp) (last_mem_prefixGroup n p)

/-- The true first moment of the actual finite positive product is the
product of the supplied free marginal first moments. -/
theorem expectation_iteratedPositiveProduct (hφ : IsTracial φ.toProbabilitySpace)
    (n : ℕ) {B : Fin n → Subalgebra ℂ A}
    (hf : FreelyIndependent φ.toProbabilitySpace B) (p : Fin n → A)
    (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, 0 ≤ p i) :
    φ.expectation (iteratedPositiveProduct n p) = ∏ i, φ.expectation (p i) := by
  induction n with
  | zero => simp [iteratedPositiveProduct, φ.toProbabilitySpace.expectation_one]
  | succ n ih =>
    rw [φ.expectation_iteratedPositiveProduct_succ hφ n hf p hpB hp,
      Fin.prod_univ_castSucc]
    rw [ih (hf.reindex Fin.castSucc (Fin.castSucc_injective n))
      (fun i => p i.castSucc) (fun i => hpB i.castSucc) (fun i => hp i.castSucc)]

/-- Nonzero marginal means give a nonzero actual iterated mean; no separate
product normalization assumption is imposed. -/
theorem expectation_iteratedPositiveProduct_ne_zero (hφ : IsTracial φ.toProbabilitySpace)
    (n : ℕ) {B : Fin n → Subalgebra ℂ A}
    (hf : FreelyIndependent φ.toProbabilitySpace B) (p : Fin n → A)
    (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, 0 ≤ p i)
    (hE : ∀ i, φ.expectation (p i) ≠ 0) :
    φ.expectation (iteratedPositiveProduct n p) ≠ 0 := by
  rw [φ.expectation_iteratedPositiveProduct hφ n hf p hpB hp]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => hE i)
end StarProbabilitySpace
end FreeProbability

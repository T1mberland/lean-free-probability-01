import FreeProbability.Algebraic.CumulantUnit
import FreeProbability.Combinatorics.NoncrossingSmall
import Mathlib.Algebra.BigOperators.Fin

/-! # Explicit first and second free cumulants -/

namespace FreeProbability

variable {𝕜 X : Type*} [Field 𝕜]

/-- The contribution of the discrete partition is the product of singleton values. -/
theorem partitionContribution_discrete (K : List X → 𝕜) (w : List X) :
    partitionContribution K w (NoncrossingPartition.discrete w.length) =
      ∏ i : Fin w.length, K [w.get i] := by
  classical
  unfold partitionContribution
  rw [Finset.prod_attach _ (fun s => K (blockWord w s)), NoncrossingPartition.blocks_discrete,
    Finset.prod_image]
  · simp only [blockWord, Finset.sort_singleton, List.map_singleton]
  · intro a _ b _ h
    exact Finset.singleton_injective h

/-- The general second free cumulant is the second moment minus the singleton product. -/
theorem freeCumulant_pair (M : List X → 𝕜) (a b : X) :
    freeCumulant M [a, b] = M [a, b] - M [a] * M [b] := by
  classical
  let : Unique (ProperNoncrossingPartition 2) := {
    default := ⟨NoncrossingPartition.discrete 2, NoncrossingPartition.discrete_two_ne_indiscrete⟩
    uniq := fun p => Subtype.ext ((p.val.two_eq_discrete_or_indiscrete).resolve_right p.property) }
  rw [freeCumulant_recursion M [a, b] (by simp)]
  congr 1
  rw [Fintype.sum_unique]
  change partitionContribution (freeCumulant M) [a, b] (NoncrossingPartition.discrete [a, b].length) = _
  rw [partitionContribution_discrete (freeCumulant M) [a, b]]
  simp [Fin.prod_univ_two, freeCumulant_singleton]

variable {A : Type*} [Ring A] [Algebra 𝕜 A]

@[simp] theorem cumulant_singleton (φ : ProbabilitySpace 𝕜 A) (a : A) :
    cumulant φ [a] = φ.expectation a := by simp [cumulant]

/-- The second free cumulant is the ordered covariance. -/
theorem cumulant_pair (φ : ProbabilitySpace 𝕜 A) (a b : A) :
    cumulant φ [a, b] = φ.expectation (a * b) - φ.expectation a * φ.expectation b := by
  simpa only [cumulant, List.prod_cons, List.prod_nil, mul_one] using
    freeCumulant_pair (fun w : List A => φ.expectation w.prod) a b

/-- For centered variables, the second univariate cumulant is the actual second moment. -/
theorem cumulant_pair_self_of_centered (φ : ProbabilitySpace 𝕜 A) (a : A)
    (ha : φ.expectation a = 0) : cumulant φ [a, a] = φ.expectation (a ^ 2) := by
  rw [cumulant_pair, ha, zero_mul, sub_zero, pow_two]

end FreeProbability

import FreeProbability.Fock.WickSuffixGramPartialSums

/-! # Finite summation by parts for actual suffix contraction operators -/
noncomputable section
open scoped BigOperators
namespace FreeProbability.Fock

/-- Division-free finite weighted contraction summation by parts. -/
theorem suffixGram_summation_by_parts {E : Type*} [AddCommGroup E] [Module ℂ E]
    (a : ℕ → E) (α : ℂ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), α ^ (2 * k) • a k) =
      α ^ (2 * n) • (∑ k ∈ Finset.range (n + 1), a k) +
      (1 - α ^ 2) • ∑ h ∈ Finset.range n,
        α ^ (2 * h) • (∑ k ∈ Finset.range (h + 1), a k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hc (P Q z : E) :
        α ^ (2 * n) • P + (1 - α ^ 2) • Q + α ^ (2 * (n + 1)) • z =
        α ^ (2 * (n + 1)) • (P + z) +
          (1 - α ^ 2) • (Q + α ^ (2 * n) • P) := by
      rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
      module
    calc
      _ = (∑ k ∈ Finset.range (n + 1), α ^ (2 * k) • a k) +
          α ^ (2 * (n + 1)) • a (n + 1) := Finset.sum_range_succ _ _
      _ = α ^ (2 * n) • (∑ k ∈ Finset.range (n + 1), a k) +
          (1 - α ^ 2) • (∑ h ∈ Finset.range n,
            α ^ (2 * h) • (∑ k ∈ Finset.range (h + 1), a k)) +
          α ^ (2 * (n + 1)) • a (n + 1) := by rw [ih]
      _ = _ := by
        rw [Finset.sum_range_succ a (n + 1)]
        rw [Finset.sum_range_succ (fun h => α ^ (2 * h) •
          (∑ k ∈ Finset.range (h + 1), a k)) n]
        exact hc _ _ _

end FreeProbability.Fock

import FreeProbability.Fock.WickMixedSuffixGramPartial

/-! # Division-free shifted mixed-degree suffix weights -/
noncomputable section
open scoped BigOperators
namespace FreeProbability.Fock

/-- Finite summation by parts with a residual degree shift, including parameter zero. -/
theorem mixedSuffix_summation_by_parts_shifted {E : Type*} [AddCommGroup E] [Module ℂ E]
    (a : ℕ → E) (α : ℂ) (m n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), α ^ (m + 2 * k) • a k) =
      α ^ (m + 2 * n) • (∑ k ∈ Finset.range (n + 1), a k) +
      (1 - α ^ 2) • ∑ h ∈ Finset.range n,
        α ^ (m + 2 * h) • (∑ k ∈ Finset.range (h + 1), a k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hc (P Q z : E) :
        α ^ (m + 2 * n) • P + (1 - α ^ 2) • Q + α ^ (m + 2 * (n + 1)) • z =
        α ^ (m + 2 * (n + 1)) • (P + z) +
          (1 - α ^ 2) • (Q + α ^ (m + 2 * n) • P) := by
      rw [show m + 2 * (n + 1) = (m + 2 * n) + 2 by omega, pow_add]
      module
    calc
      _ = (∑ k ∈ Finset.range (n + 1), α ^ (m + 2 * k) • a k) +
          α ^ (m + 2 * (n + 1)) • a (n + 1) := Finset.sum_range_succ _ _
      _ = α ^ (m + 2 * n) • (∑ k ∈ Finset.range (n + 1), a k) +
          (1 - α ^ 2) • (∑ h ∈ Finset.range n,
            α ^ (m + 2 * h) • (∑ k ∈ Finset.range (h + 1), a k)) +
          α ^ (m + 2 * (n + 1)) • a (n + 1) := by rw [ih]
      _ = _ := by
        rw [Finset.sum_range_succ a (n + 1)]
        rw [Finset.sum_range_succ (fun h => α ^ (m + 2 * h) •
          (∑ k ∈ Finset.range (h + 1), a k)) n]
        exact hc _ _ _


end FreeProbability.Fock

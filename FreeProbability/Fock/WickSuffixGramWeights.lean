import FreeProbability.Fock.WickSuffixGramContractions

/-! # Division-free telescoping of the positive suffix coefficients -/
noncomputable section
open scoped BigOperators
namespace FreeProbability.Fock

/-- Exact coefficient telescoping, including the endpoint zero with `0^0 = 1`.
Here `m` is the residual word degree and `j` the common suffix length. -/
theorem suffixGram_weight_telescoping (α : ℝ) (m j : ℕ) :
    α ^ (m + 2 * j) + (1 - α ^ 2) *
      ∑ h ∈ Finset.range j, α ^ (m + 2 * h) = α ^ m := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ]
    have hp : α ^ (m + 2 * (j + 1)) = α ^ (m + 2 * j) * α ^ 2 := by
      rw [show m + 2 * (j + 1) = (m + 2 * j) + 2 by omega, pow_add]
    rw [hp]
    calc
      α ^ (m + 2 * j) * α ^ 2 + (1 - α ^ 2) *
          ((∑ h ∈ Finset.range j, α ^ (m + 2 * h)) + α ^ (m + 2 * j)) =
        α ^ (m + 2 * j) + (1 - α ^ 2) *
          ∑ h ∈ Finset.range j, α ^ (m + 2 * h) := by ring
      _ = α ^ m := ih

/-- All finite suffix coefficients are nonnegative for genuine contraction parameters. -/
theorem suffixGram_weight_nonneg {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (m : ℕ) :
    0 ≤ (1 - α ^ 2) * α ^ m := by
  have hsq : α ^ 2 ≤ 1 := by nlinarith
  exact mul_nonneg (sub_nonneg.mpr hsq) (pow_nonneg hα m)

end FreeProbability.Fock

import FreeProbability.Fock.WickMixedSuffixGramWeights

/-! # Exact real-parameter pairwise suffix Gram identity at arbitrary degrees -/
noncomputable section
open scoped Classical BigOperators
namespace FreeProbability.Fock
variable {I : Type*}

/-- Pairwise mixed-degree suffix identity with actual bounded Wick products.
The parameter is real, in preparation for the adjointed amplitude weights. -/
theorem wick_mixed_damped_suffix_Gram (u v : List I) (n : ℕ)
    (hn : n = min u.length v.length) (α : ℝ) :
    (∑ i ∈ Finset.range (n + 1), (α : ℂ) ^ (u.length + v.length - 2 * n + 2 * i) •
      (if u.drop (u.length - (n - i)) = v.drop (v.length - (n - i)) then
        wick (u.take (u.length - (n - i)) ++ (v.take (v.length - (n - i))).reverse) else 0)) =
      (α : ℂ) ^ (u.length + v.length) • (wick u * star (wick v)) +
      (1 - (α : ℂ) ^ 2) • ∑ i ∈ Finset.range n,
        (α : ℂ) ^ (u.length + v.length - 2 * n + 2 * i) •
          (if u.drop (u.length - (n - i)) = v.drop (v.length - (n - i)) then
            wick (u.take (u.length - (n - i))) *
              star (wick (v.take (v.length - (n - i)))) else 0) := by
  have htotal : (∑ i ∈ Finset.range (n + 1),
      if u.drop (u.length - (n - i)) = v.drop (v.length - (n - i)) then
        wick (u.take (u.length - (n - i)) ++ (v.take (v.length - (n - i))).reverse) else 0) =
      wick u * star (wick v) := by
    rw [← mixedSuffix_prefix_Gram_partial u v n n hn le_rfl]
    simp
  rw [mixedSuffix_summation_by_parts_shifted
    (fun i => if u.drop (u.length - (n - i)) = v.drop (v.length - (n - i)) then
      wick (u.take (u.length - (n - i)) ++ (v.take (v.length - (n - i))).reverse) else 0)
    (α : ℂ) (u.length + v.length - 2 * n) n, htotal]
  have he : u.length + v.length - 2 * n + 2 * n = u.length + v.length := by omega
  rw [he]
  congr 1
  apply congrArg (fun z => (1 - (α : ℂ) ^ 2) • z)
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i ≤ n := (Finset.mem_range.mp hi).le
  rw [← mixedSuffix_prefix_Gram_partial u v n i hn hin]

end FreeProbability.Fock

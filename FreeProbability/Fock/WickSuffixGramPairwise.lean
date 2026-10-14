import FreeProbability.Fock.WickSuffixGramSummation

/-! # Exact homogeneous pairwise suffix Gram decomposition

This is an actual operator identity. Its left side is the literal degree-damped
contraction polynomial; linking the full matrix amplitude to actual OU is separate.
-/
noncomputable section
open scoped Classical BigOperators
namespace FreeProbability.Fock
variable {I : Type*}

/-- The exact homogeneous pairwise positive-suffix algebraic identity. -/
theorem wick_damped_equalDegree_suffix_Gram (u v : List I) (hl : u.length = v.length)
    (α : ℂ) :
    (∑ k ∈ Finset.range (u.length + 1), α ^ (2 * k) •
      (if u.drop k = v.drop k then wick (u.take k ++ (v.take k).reverse) else 0)) =
      α ^ (2 * u.length) • (wick u * star (wick v)) +
      (1 - α ^ 2) • ∑ h ∈ Finset.range u.length, α ^ (2 * h) •
        (if u.drop h = v.drop h then wick (u.take h) * star (wick (v.take h)) else 0) := by
  rw [suffixGram_summation_by_parts
    (fun k => if u.drop k = v.drop k then wick (u.take k ++ (v.take k).reverse) else 0)
    α u.length]
  rw [← wick_mul_star_equalDegree_range u v hl]
  congr 1
  apply congrArg (fun z => (1 - α ^ 2) • z)
  apply Finset.sum_congr rfl
  intro h hh
  have hle : h ≤ u.length := (Finset.mem_range.mp hh).le
  rw [← commonSuffix_prefix_Gram_partial u v hl h hle]

end FreeProbability.Fock

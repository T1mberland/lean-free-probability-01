import FreeProbability.Fock.WickMixedSuffixGramPairwise

/-! # Real mixed suffix weights in literal nonempty suffix length order -/
noncomputable section
open scoped Classical BigOperators
namespace FreeProbability.Fock
variable {I : Type*}

/-- Exact mixed real-parameter pairwise identity indexed by suffix length.
The nonempty suffix sum is j+1, and no division by α occurs. -/
theorem wick_mixed_suffix_Gram_lengths (u v : List I) (α : ℝ) :
    (∑ j ∈ Finset.range (min u.length v.length + 1),
      (α : ℂ) ^ (u.length + v.length - 2 * j) •
        (if u.drop (u.length - j) = v.drop (v.length - j) then
          wick (u.take (u.length - j) ++ (v.take (v.length - j)).reverse) else 0)) =
      (α : ℂ) ^ (u.length + v.length) • (wick u * star (wick v)) +
      (1 - (α : ℂ) ^ 2) • ∑ j ∈ Finset.range (min u.length v.length),
        (α : ℂ) ^ (u.length + v.length - 2 * (j + 1)) •
          (if u.drop (u.length - (j + 1)) = v.drop (v.length - (j + 1)) then
            wick (u.take (u.length - (j + 1))) *
              star (wick (v.take (v.length - (j + 1)))) else 0) := by
  let n := min u.length v.length
  have hleft :
      (∑ i ∈ Finset.range (n + 1), (α : ℂ) ^ (u.length + v.length - 2 * n + 2 * i) •
        (if u.drop (u.length - (n - i)) = v.drop (v.length - (n - i)) then
          wick (u.take (u.length - (n - i)) ++ (v.take (v.length - (n - i))).reverse) else 0)) =
      ∑ j ∈ Finset.range (n + 1), (α : ℂ) ^ (u.length + v.length - 2 * j) •
        (if u.drop (u.length - j) = v.drop (v.length - j) then
          wick (u.take (u.length - j) ++ (v.take (v.length - j)).reverse) else 0) := by
    rw [← Finset.sum_range_reflect (fun i =>
      (α : ℂ) ^ (u.length + v.length - 2 * n + 2 * i) •
        (if u.drop (u.length - (n - i)) = v.drop (v.length - (n - i)) then
          wick (u.take (u.length - (n - i)) ++ (v.take (v.length - (n - i))).reverse) else 0)) (n + 1)]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j ≤ n := by have := Finset.mem_range.mp hj; omega
    have he : n - (n - j) = j := by omega
    have hp : u.length + v.length - 2 * n + 2 * (n - j) = u.length + v.length - 2 * j := by dsimp [n]; omega
    simp only [Nat.add_sub_cancel, he, hp]
  have hright :
      (∑ i ∈ Finset.range n, (α : ℂ) ^ (u.length + v.length - 2 * n + 2 * i) •
        (if u.drop (u.length - (n - i)) = v.drop (v.length - (n - i)) then
          wick (u.take (u.length - (n - i))) * star (wick (v.take (v.length - (n - i)))) else 0)) =
      ∑ j ∈ Finset.range n, (α : ℂ) ^ (u.length + v.length - 2 * (j + 1)) •
        (if u.drop (u.length - (j + 1)) = v.drop (v.length - (j + 1)) then
          wick (u.take (u.length - (j + 1))) * star (wick (v.take (v.length - (j + 1)))) else 0) := by
    rw [← Finset.sum_range_reflect (fun i =>
      (α : ℂ) ^ (u.length + v.length - 2 * n + 2 * i) •
        (if u.drop (u.length - (n - i)) = v.drop (v.length - (n - i)) then
          wick (u.take (u.length - (n - i))) * star (wick (v.take (v.length - (n - i)))) else 0)) n]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j < n := Finset.mem_range.mp hj
    have he : n - (n - 1 - j) = j + 1 := by omega
    have hp : u.length + v.length - 2 * n + 2 * (n - 1 - j) =
        u.length + v.length - 2 * (j + 1) := by dsimp [n]; omega
    simp only [he, hp]
  have hh := wick_mixed_damped_suffix_Gram u v n rfl α
  rw [hleft, hright] at hh
  exact hh

end FreeProbability.Fock

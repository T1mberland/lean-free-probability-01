import FreeProbability.Fock.WickSuffixGramHomogeneous

/-! # Genuine truncated-prefix Gram operators as partial contraction sums -/
noncomputable section
open scoped Classical BigOperators
namespace FreeProbability.Fock
variable {I : Type*}

theorem wick_mul_star_equalDegree_range (u v : List I) (h : u.length = v.length) :
    wick u * star (wick v) = ∑ k ∈ Finset.range (u.length + 1),
      if u.drop k = v.drop k then wick (u.take k ++ (v.take k).reverse) else 0 := by
  rw [wick_mul_star_equalDegree u v h]
  exact Fin.sum_univ_eq_sum_range
    (fun k => if u.drop k = v.drop k then wick (u.take k ++ (v.take k).reverse) else 0)
    (u.length + 1)

/-- Equality of an earlier terminal cut implies equality at every later cut. -/
theorem commonSuffix_drop_mono {u v : List I} {k h : ℕ} (hk : k ≤ h)
    (hs : u.drop k = v.drop k) : u.drop h = v.drop h := by
  have hh := congrArg (List.drop (h - k)) hs
  simpa only [List.drop_drop, Nat.add_sub_of_le hk] using hh

/-- Each actual truncated-prefix Gram is exactly the partial contraction sum. -/
theorem commonSuffix_prefix_Gram_partial (u v : List I) (hl : u.length = v.length)
    (h : ℕ) (hh : h ≤ u.length) :
    (if u.drop h = v.drop h then wick (u.take h) * star (wick (v.take h)) else 0) =
      ∑ k ∈ Finset.range (h + 1),
        if u.drop k = v.drop k then wick (u.take k ++ (v.take k).reverse) else 0 := by
  by_cases hs : u.drop h = v.drop h
  · simp only [hs, ite_true]
    have hlen : (u.take h).length = h := by simp [List.length_take, Nat.min_eq_left hh]
    have hvlen : (v.take h).length = h := by rw [List.length_take, ← hl]; omega
    rw [wick_mul_star_equalDegree_range _ _ (hlen.trans hvlen.symm), hlen]
    apply Finset.sum_congr rfl
    intro k hk
    have hkh : k ≤ h := by have := Finset.mem_range.mp hk; omega
    simp only [commonSuffix_prefix_drop_iff hkh hs, List.take_take,
      Nat.min_eq_left hkh]
  · simp only [hs, ite_false]
    symm
    apply Finset.sum_eq_zero
    intro k hk
    have hkh : k ≤ h := by have := Finset.mem_range.mp hk; omega
    have hn : u.drop k ≠ v.drop k := fun he => hs (commonSuffix_drop_mono hkh he)
    simp [hn]

end FreeProbability.Fock

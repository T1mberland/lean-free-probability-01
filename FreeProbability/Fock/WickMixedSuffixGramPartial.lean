import FreeProbability.Fock.WickMixedSuffixGramContractions

/-! # Exact nested-prefix Gram sums for mixed word degrees -/
noncomputable section
open scoped Classical BigOperators
namespace FreeProbability.Fock
variable {I : Type*}

/-- Every shorter terminal cut of an actual common suffix is also common. -/
theorem mixedSuffix_shorter {u v : List I} {j k : ℕ} (hkj : k ≤ j)
    (hju : j ≤ u.length) (hjv : j ≤ v.length)
    (hs : u.drop (u.length - j) = v.drop (v.length - j)) :
    u.drop (u.length - k) = v.drop (v.length - k) := by
  have hh := congrArg (List.drop (j - k)) hs
  rw [List.drop_drop, List.drop_drop] at hh
  have hu : u.length - j + (j - k) = u.length - k := by omega
  have hv : v.length - j + (j - k) = v.length - k := by omega
  simpa only [hu, hv] using hh

/-- Actual products of unequal prefixes are partial sums of the same residual contractions. -/
theorem mixedSuffix_prefix_Gram_partial (u v : List I) (n i : ℕ)
    (hn : n = min u.length v.length) (hi : i ≤ n) :
    (if u.drop (u.length - (n - i)) = v.drop (v.length - (n - i)) then
      wick (u.take (u.length - (n - i))) * star (wick (v.take (v.length - (n - i)))) else 0) =
      ∑ k ∈ Finset.range (i + 1),
        if u.drop (u.length - (n - k)) = v.drop (v.length - (n - k)) then
          wick (u.take (u.length - (n - k)) ++ (v.take (v.length - (n - k))).reverse) else 0 := by
  have hnu : n ≤ u.length := by omega
  have hnv : n ≤ v.length := by omega
  let pu := u.length - (n - i)
  let pv := v.length - (n - i)
  have hpu : pu ≤ u.length := by omega
  have hpv : pv ≤ v.length := by omega
  have hlu : (u.take pu).length = pu := by simp [List.length_take, Nat.min_eq_left hpu]
  have hlv : (v.take pv).length = pv := by simp [List.length_take, Nat.min_eq_left hpv]
  have hmin : min pu pv = i := by dsimp [pu, pv]; omega
  by_cases hs : u.drop pu = v.drop pv
  · simp only [show u.drop (u.length - (n - i)) = v.drop (v.length - (n - i)) from hs, ite_true]
    change wick (u.take pu) * star (wick (v.take pv)) = _
    rw [wick_mul_star_mixed_suffix_min, hlu, hlv, hmin]
    rw [← Finset.sum_range_reflect (fun j =>
      if (u.take pu).drop (pu - j) = (v.take pv).drop (pv - j) then
        wick ((u.take pu).take (pu - j) ++ ((v.take pv).take (pv - j)).reverse) else 0) (i + 1)]
    apply Finset.sum_congr rfl
    intro k hk
    have hki : k ≤ i := by have := Finset.mem_range.mp hk; omega
    have hu : pu - (i - k) = u.length - (n - k) := by dsimp [pu]; omega
    have hv : pv - (i - k) = v.length - (n - k) := by dsimp [pv]; omega
    have hku : u.length - (n - k) ≤ pu := by dsimp [pu]; omega
    have hkv : v.length - (n - k) ≤ pv := by dsimp [pv]; omega
    simp only [Nat.add_sub_cancel, hu, hv, mixedSuffix_prefix_drop_iff hku hkv hs,
      List.take_take, Nat.min_eq_left hku, Nat.min_eq_left hkv]
  · simp only [show ¬ u.drop (u.length - (n - i)) = v.drop (v.length - (n - i)) from hs, ite_false]
    symm
    apply Finset.sum_eq_zero
    intro k hk
    have hki : k ≤ i := by have := Finset.mem_range.mp hk; omega
    have hh : ¬ u.drop (u.length - (n - k)) = v.drop (v.length - (n - k)) := by
      intro he
      exact hs (mixedSuffix_shorter (by omega) (by omega) (by omega) he)
    simp only [hh, ite_false]

end FreeProbability.Fock

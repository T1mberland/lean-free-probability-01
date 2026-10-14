import FreeProbability.Fock.WickSuffixGramOrder

/-! # Actual common-suffix contraction lengths for words of arbitrary degrees -/
noncomputable section
open scoped Classical BigOperators
namespace FreeProbability.Fock
variable {I : Type*}

/-- The equal-terminal-word condition encodes the actual suffix at contraction length j. -/
theorem mixedSuffix_cut_iff (u v : List I) (j : ℕ) (hj : j ≤ u.length) :
    (u.drop (u.length - j)).IsSuffix v ↔
      u.drop (u.length - j) = v.drop (v.length - j) := by
  rw [List.suffix_iff_eq_drop, List.length_drop]
  have he : u.length - (u.length - j) = j := by omega
  rw [he]

/-- Actual bounded Wick products indexed by common suffix length, without equal-degree assumptions. -/
theorem wick_mul_star_mixed_suffix (u v : List I) :
    wick u * star (wick v) = ∑ j ∈ Finset.range (u.length + 1),
      if u.drop (u.length - j) = v.drop (v.length - j) then
        wick (u.take (u.length - j) ++ (v.take (v.length - j)).reverse) else 0 := by
  rw [wick_mul_star_common_suffix]
  rw [Fin.sum_univ_eq_sum_range (fun k => if (u.drop k).IsSuffix v then
    wick (u.take k ++ (v.take (v.length - (u.length - k))).reverse) else 0) (u.length + 1)]
  rw [← Finset.sum_range_reflect (fun k => if (u.drop k).IsSuffix v then
    wick (u.take k ++ (v.take (v.length - (u.length - k))).reverse) else 0) (u.length + 1)]
  apply Finset.sum_congr rfl
  intro j hj
  have hjle : j ≤ u.length := by have := Finset.mem_range.mp hj; omega
  have he : u.length - (u.length - j) = j := by omega
  simp only [Nat.add_sub_cancel, mixedSuffix_cut_iff u v j hjle, he]

/-- A surviving contraction length automatically lies below both actual word degrees. -/
theorem mixedSuffix_length_le {u v : List I} {j : ℕ} (hj : j ≤ u.length)
    (hs : u.drop (u.length - j) = v.drop (v.length - j)) : j ≤ v.length := by
  have hh := congrArg List.length hs
  simp only [List.length_drop] at hh
  omega

/-- Symmetric actual contraction range, valid also when one of the words is empty. -/
theorem wick_mul_star_mixed_suffix_min (u v : List I) :
    wick u * star (wick v) = ∑ j ∈ Finset.range (min u.length v.length + 1),
      if u.drop (u.length - j) = v.drop (v.length - j) then
        wick (u.take (u.length - j) ++ (v.take (v.length - j)).reverse) else 0 := by
  rw [wick_mul_star_mixed_suffix]
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right (Nat.min_le_left _ _) 1))
  intro j hj hn
  have hju : j ≤ u.length := by have := Finset.mem_range.mp hj; omega
  have hnot : ¬ u.drop (u.length - j) = v.drop (v.length - j) := by
    intro hs
    have hjv := mixedSuffix_length_le hju hs
    apply hn
    exact Finset.mem_range.mpr (by omega)
  simp only [hnot, ite_false]

/-- Exact terminal-cut tests on two unequal prefixes after a shared suffix is removed. -/
theorem mixedSuffix_prefix_drop_iff {u v : List I} {pu pv ku kv : ℕ}
    (hu : ku ≤ pu) (hv : kv ≤ pv) (hs : u.drop pu = v.drop pv) :
    (u.take pu).drop ku = (v.take pv).drop kv ↔ u.drop ku = v.drop kv := by
  have hau : (u.take pu).drop ku ++ u.drop pu = u.drop ku := by
    rw [List.drop_take]
    have ha := List.take_append_drop (pu - ku) (u.drop ku)
    simpa only [List.drop_drop, Nat.add_sub_of_le hu] using ha
  have hav : (v.take pv).drop kv ++ v.drop pv = v.drop kv := by
    rw [List.drop_take]
    have ha := List.take_append_drop (pv - kv) (v.drop kv)
    simpa only [List.drop_drop, Nat.add_sub_of_le hv] using ha
  constructor
  · intro hp
    rw [← hau, ← hav, hp, hs]
  · intro hp
    apply List.append_cancel_right (bs := u.drop pu)
    rw [hau, hp, hs, hav]

end FreeProbability.Fock

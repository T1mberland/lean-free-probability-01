import FreeProbability.Fock.WickSuffixGramMatrixProduct

/-! # Exact common-cut formula at homogeneous word degree -/
noncomputable section
open scoped Classical BigOperators
namespace FreeProbability.Fock
variable {I : Type*}

/-- At equal degree a suffix condition is exactly equality of the two terminal cuts. -/
theorem equalDegree_suffix_iff {u v : List I} (h : u.length = v.length)
    {k : ℕ} (hk : k ≤ u.length) :
    (u.drop k).IsSuffix v ↔ u.drop k = v.drop k := by
  rw [List.suffix_iff_eq_drop, List.length_drop]
  have he : v.length - (u.length - k) = k := by omega
  rw [he]

/-- Homogeneous actual Wick products contract precisely identical suffixes.
The surviving prefixes have the same length and the matrix coefficient order
is supplied separately by `matrixWickTerm_mul_star`. -/
theorem wick_mul_star_equalDegree (u v : List I) (h : u.length = v.length) :
    wick u * star (wick v) = ∑ k : Fin (u.length + 1),
      if u.drop k.val = v.drop k.val then
        wick (u.take k.val ++ (v.take k.val).reverse) else 0 := by
  rw [wick_mul_star_common_suffix]
  apply Finset.sum_congr rfl
  intro k _
  have hk : k.val ≤ u.length := by omega
  have he : v.length - (u.length - k.val) = k.val := by omega
  simp only [equalDegree_suffix_iff h hk, he]

/-- Removing an already common suffix leaves the exact same earlier
contraction tests on the two prefixes. -/
theorem commonSuffix_prefix_drop_iff {u v : List I} {k h : ℕ}
    (hk : k ≤ h) (hs : u.drop h = v.drop h) :
    (u.take h).drop k = (v.take h).drop k ↔ u.drop k = v.drop k := by
  have hu : (u.take h).drop k ++ u.drop h = u.drop k := by
    rw [List.drop_take]
    have ha := List.take_append_drop (h - k) (u.drop k)
    simpa only [List.drop_drop, Nat.add_sub_of_le hk] using ha
  have hv : (v.take h).drop k ++ v.drop h = v.drop k := by
    rw [List.drop_take]
    have ha := List.take_append_drop (h - k) (v.drop k)
    simpa only [List.drop_drop, Nat.add_sub_of_le hk] using ha
  constructor
  · intro hp
    rw [← hu, ← hv, hp, hs]
  · intro hp
    apply List.append_cancel_right (bs := u.drop h)
    rw [hu, hp, hs, hv]

end FreeProbability.Fock

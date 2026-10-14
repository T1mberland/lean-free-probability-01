import FreeProbability.Fock.WickMixedSuffixGramLengths

/-! # Exact finite bijection between contraction lengths and nonempty common suffixes -/
noncomputable section
open scoped Classical BigOperators
namespace FreeProbability.Fock
variable {I A : Type*} [AddCommMonoid A]

/-- Generic exact finite reindexing by actual nonempty common terminal words. -/
theorem mixedSuffix_nonempty_sum (u v : List I) (f : List I → A) :
    (∑ j ∈ Finset.range (min u.length v.length),
      if u.drop (u.length - (j + 1)) = v.drop (v.length - (j + 1)) then
        f (u.drop (u.length - (j + 1))) else 0) =
      ∑ s ∈ u.tails.toFinset.erase [], if s.IsSuffix v then f s else 0 := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_bij (fun j _ => u.drop (u.length - (j + 1)))
  · intro j hj
    obtain ⟨hj, hs⟩ := Finset.mem_filter.mp hj
    have hjm := Finset.mem_range.mp hj
    have hju : j + 1 ≤ u.length := by omega
    have hlen : (u.drop (u.length - (j + 1))).length = j + 1 := by simp only [List.length_drop]; omega
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_erase.mpr
      constructor
      · intro he
        have := congrArg List.length he
        simp only [List.length_nil, hlen] at this
        omega
      · exact List.mem_toFinset.mpr ((List.mem_tails _ _).mpr (List.drop_suffix _ _))
    · exact (mixedSuffix_cut_iff u v (j + 1) hju).mpr hs
  · intro j hj k hk he
    have hjm := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    have hkm := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    have hh := congrArg List.length he
    simp only [List.length_drop] at hh
    omega
  · intro s hs
    obtain ⟨hs, hv⟩ := Finset.mem_filter.mp hs
    obtain ⟨hne, hs⟩ := Finset.mem_erase.mp hs
    have hu : s.IsSuffix u := (List.mem_tails _ _).mp (List.mem_toFinset.mp hs)
    have hlu := hu.length_le
    have hlv := hv.length_le
    have hpos : 0 < s.length := List.length_pos_iff.mpr hne
    have hj : s.length - 1 + 1 = s.length := by omega
    refine ⟨s.length - 1, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_range.mpr (by omega)
      · rw [hj, ← List.suffix_iff_eq_drop.mp hu, ← List.suffix_iff_eq_drop.mp hv]
    · rw [hj]
      exact (List.suffix_iff_eq_drop.mp hu).symm
  · intro j hj
    rfl

end FreeProbability.Fock

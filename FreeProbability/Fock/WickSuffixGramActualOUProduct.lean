import FreeProbability.Fock.WickSuffixGramActualOU

/-! # Actual OU on homogeneous closed Wick products -/
noncomputable section
open scoped Classical BigOperators
namespace FreeProbability.Fock
variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Actual homogeneous Wick contractions inside the literal word C-star closure. -/
theorem suffixGramClosedWick_mul_star (u v : List I) (hl : u.length = v.length) :
    suffixGramClosedWick u * star (suffixGramClosedWick v) =
      ∑ k ∈ Finset.range (u.length + 1), if u.drop k = v.drop k then
        suffixGramClosedWick (u.take k ++ (v.take k).reverse) else 0 := by
  apply Subtype.ext
  change (closedSemicircularAlgebra I).subtype
    (suffixGramClosedWick u * star (suffixGramClosedWick v)) =
      (closedSemicircularAlgebra I).subtype _
  simp only [map_mul, map_star, map_sum, apply_ite, map_zero]
  exact wick_mul_star_equalDegree_range u v hl

/-- The genuine prescribed-family OU map, on an actual product of homogeneous Wick words. -/
theorem actualFamilyWordOU_Wick_mul_star (e : I → H) (he : Orthonormal ℂ e)
    (t : ℝ) (ht : 0 ≤ t) (u v : List I) (hl : u.length = v.length) :
    actualFamilyWordOU e he t ht (suffixGramClosedWick u * star (suffixGramClosedWick v)) =
      ∑ k ∈ Finset.range (u.length + 1), (Real.exp (-t) : ℂ) ^ (2 * k) •
        (if u.drop k = v.drop k then wick (u.take k ++ (v.take k).reverse) else 0) := by
  rw [suffixGramClosedWick_mul_star u v hl, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hku : k ≤ u.length := by have := Finset.mem_range.mp hk; omega
  have hkv : k ≤ v.length := by omega
  by_cases hs : u.drop k = v.drop k
  · simp only [hs, ite_true, actualFamilyWordOU_closedWick]
    congr 1
    simp only [degreeWeight, List.length_append, List.length_reverse, List.length_take,
      Nat.min_eq_left hku, Nat.min_eq_left hkv]
    congr 1
    omega
  · simp only [hs, ite_false, map_zero]
    exact (smul_zero (M := ℂ) (A := WordSpace I →L[ℂ] WordSpace I)
      ((Real.exp (-t) : ℂ) ^ (2 * k))).symm

end FreeProbability.Fock

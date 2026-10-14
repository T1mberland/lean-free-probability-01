import FreeProbability.Fock.WickMixedSuffixGramSuffixSums

/-! # Genuine prescribed-family OU images of arbitrary mixed Wick products -/
noncomputable section
open scoped Classical BigOperators
namespace FreeProbability.Fock
variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- General actual Wick contractions inside the canonical word norm closure. -/
theorem suffixGramClosedWick_mul_star_mixed (u v : List I) :
    suffixGramClosedWick u * star (suffixGramClosedWick v) =
      ∑ j ∈ Finset.range (min u.length v.length + 1),
        if u.drop (u.length - j) = v.drop (v.length - j) then
          suffixGramClosedWick (u.take (u.length - j) ++ (v.take (v.length - j)).reverse) else 0 := by
  apply Subtype.ext
  change (closedSemicircularAlgebra I).subtype
    (suffixGramClosedWick u * star (suffixGramClosedWick v)) =
      (closedSemicircularAlgebra I).subtype _
  simp only [map_mul, map_star, map_sum, apply_ite, map_zero]
  exact wick_mul_star_mixed_suffix_min u v

/-- The actual transported OU map of a mixed product is its exact damped contraction polynomial. -/
theorem actualFamilyWordOU_Wick_mul_star_mixed (e : I → H) (he : Orthonormal ℂ e)
    (t : ℝ) (ht : 0 ≤ t) (u v : List I) :
    actualFamilyWordOU e he t ht (suffixGramClosedWick u * star (suffixGramClosedWick v)) =
      ∑ j ∈ Finset.range (min u.length v.length + 1),
        (Real.exp (-t) : ℂ) ^ (u.length + v.length - 2 * j) •
          (if u.drop (u.length - j) = v.drop (v.length - j) then
            wick (u.take (u.length - j) ++ (v.take (v.length - j)).reverse) else 0) := by
  rw [suffixGramClosedWick_mul_star_mixed, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjm : j ≤ min u.length v.length := by have := Finset.mem_range.mp hj; omega
  by_cases hs : u.drop (u.length - j) = v.drop (v.length - j)
  · simp only [hs, ite_true, actualFamilyWordOU_closedWick]
    congr 1
    simp only [degreeWeight, List.length_append, List.length_reverse, List.length_take,
      Nat.min_eq_left (Nat.sub_le u.length j), Nat.min_eq_left (Nat.sub_le v.length j)]
    congr 1
    omega
  · simp only [hs, ite_false, map_zero]
    exact (smul_zero (M := ℂ) (A := WordSpace I →L[ℂ] WordSpace I)
      ((Real.exp (-t) : ℂ) ^ (u.length + v.length - 2 * j))).symm

/-- True actual OU equals the mixed pairwise prefix Gram expansion, with real damping. -/
theorem actualFamilyWordOU_mixed_suffix_Gram_lengths (e : I → H) (he : Orthonormal ℂ e)
    (t : ℝ) (ht : 0 ≤ t) (u v : List I) :
    actualFamilyWordOU e he t ht (suffixGramClosedWick u * star (suffixGramClosedWick v)) =
      (Real.exp (-t) : ℂ) ^ (u.length + v.length) • (wick u * star (wick v)) +
      (1 - (Real.exp (-t) : ℂ) ^ 2) • ∑ j ∈ Finset.range (min u.length v.length),
        (Real.exp (-t) : ℂ) ^ (u.length + v.length - 2 * (j + 1)) •
          (if u.drop (u.length - (j + 1)) = v.drop (v.length - (j + 1)) then
            wick (u.take (u.length - (j + 1))) *
              star (wick (v.take (v.length - (j + 1)))) else 0) := by
  rw [actualFamilyWordOU_Wick_mul_star_mixed]
  exact wick_mixed_suffix_Gram_lengths u v (Real.exp (-t))

end FreeProbability.Fock

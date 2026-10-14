import FreeProbability.Fock.WickMixedSuffixGramActualOU

/-! # Real adjoint amplitude weights and actual common-suffix sums -/
noncomputable section
open scoped Classical BigOperators
namespace FreeProbability.Fock

/-- Real scalar powers remain unchanged under adjoint, so amplitude star weights multiply correctly. -/
theorem real_scaled_mul_star_power {A : Type*} [Ring A] [StarRing A]
    [Algebra ℂ A] [StarModule ℂ A] (α : ℝ) (a b : ℕ) (T U : A) :
    ((α : ℂ) ^ a • T) * star ((α : ℂ) ^ b • U) =
      (α : ℂ) ^ (a + b) • (T * star U) := by
  have hs : star ((α : ℂ) ^ b) = (α : ℂ) ^ b := by simp
  simp only [star_smul, hs, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [mul_comm, ← pow_add]

variable {I : Type*}
/-- The weighted contraction sum is exactly the sum over the actual nonempty common suffixes. -/
theorem mixedSuffix_weighted_sum (u v : List I) (α : ℝ) :
    (∑ j ∈ Finset.range (min u.length v.length),
      (α : ℂ) ^ (u.length + v.length - 2 * (j + 1)) •
        (if u.drop (u.length - (j + 1)) = v.drop (v.length - (j + 1)) then
          wick (u.take (u.length - (j + 1))) * star (wick (v.take (v.length - (j + 1)))) else 0)) =
      ∑ s ∈ u.tails.toFinset.erase [], if s.IsSuffix v then
        (α : ℂ) ^ (u.length + v.length - 2 * s.length) •
          (wick (u.take (u.length - s.length)) * star (wick (v.take (v.length - s.length)))) else 0 := by
  let f := fun s : List I => (α : ℂ) ^ (u.length + v.length - 2 * s.length) •
    (wick (u.take (u.length - s.length)) * star (wick (v.take (v.length - s.length))))
  rw [← mixedSuffix_nonempty_sum u v f]
  apply Finset.sum_congr rfl
  intro j hj
  have hjm : j < min u.length v.length := Finset.mem_range.mp hj
  have hlenv : (v.drop (v.length - (j + 1))).length = j + 1 := by simp only [List.length_drop]; omega
  by_cases hs : u.drop (u.length - (j + 1)) = v.drop (v.length - (j + 1))
  · simp only [hs, ite_true, f, hlenv]
  · simp only [hs, ite_false]
    exact smul_zero (M := ℂ) (A := WordSpace I →L[ℂ] WordSpace I) _

/-- Genuine actual OU pairwise mixed product expansion over terminal words. -/
theorem actualFamilyWordOU_mixed_suffix_Gram {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (e : I → H) (he : Orthonormal ℂ e)
    (t : ℝ) (ht : 0 ≤ t) (u v : List I) :
    actualFamilyWordOU e he t ht (suffixGramClosedWick u * star (suffixGramClosedWick v)) =
      (Real.exp (-t) : ℂ) ^ (u.length + v.length) • (wick u * star (wick v)) +
      (1 - (Real.exp (-t) : ℂ) ^ 2) • ∑ s ∈ u.tails.toFinset.erase [],
        if s.IsSuffix v then (Real.exp (-t) : ℂ) ^ (u.length + v.length - 2 * s.length) •
          (wick (u.take (u.length - s.length)) * star (wick (v.take (v.length - s.length)))) else 0 := by
  rw [actualFamilyWordOU_mixed_suffix_Gram_lengths, mixedSuffix_weighted_sum]

end FreeProbability.Fock

import FreeProbability.Fock.WickMixedSuffixGramMatrix

/-! # Genuine real-weighted matrix residual-prefix terms -/
noncomputable section
open scoped Classical BigOperators
namespace FreeProbability.Fock
variable {I ν : Type*} [Fintype ν]

/-- The actual matrix residual-prefix term, with a real damping parameter. -/
def mixedMatrixPrefixTerm (C : Matrix ν ν ℂ) (u : List I) (α : ℝ) (s : List I) :
    CStarMatrix ν ν (WordSpace I →L[ℂ] WordSpace I) :=
  if s.IsSuffix u then (α : ℂ) ^ (u.length - s.length) •
    matrixWickTerm C (u.take (u.length - s.length)) else 0

omit [Fintype ν] in
@[simp] theorem mixedMatrixPrefixTerm_nil (C : Matrix ν ν ℂ) (u : List I) (α : ℝ) :
    mixedMatrixPrefixTerm C u α [] = (α : ℂ) ^ u.length • matrixWickTerm C u := by
  simp [mixedMatrixPrefixTerm]

/-- Adjointed real amplitude weights give exactly the mixed suffix coefficient. -/
theorem mixedMatrixPrefixTerm_mul_star (C D : Matrix ν ν ℂ) (u v s : List I) (α : ℝ)
    (hu : s.IsSuffix u) :
    mixedMatrixPrefixTerm C u α s * star (mixedMatrixPrefixTerm D v α s) =
      if s.IsSuffix v then (α : ℂ) ^ (u.length + v.length - 2 * s.length) •
        (matrixWickTerm C (u.take (u.length - s.length)) *
          star (matrixWickTerm D (v.take (v.length - s.length)))) else 0 := by
  by_cases hv : s.IsSuffix v
  · simp only [mixedMatrixPrefixTerm, hu, hv, ite_true]
    have hm := real_scaled_mul_star_power α (u.length - s.length) (v.length - s.length)
      (matrixWickTerm C (u.take (u.length - s.length)))
      (matrixWickTerm D (v.take (v.length - s.length)))
    have he : u.length - s.length + (v.length - s.length) =
        u.length + v.length - 2 * s.length := by have := hu.length_le; have := hv.length_le; omega
    rw [he] at hm
    exact hm
  · simp only [mixedMatrixPrefixTerm, hu, hv, ite_true, ite_false]
    rw [star_zero (CStarMatrix ν ν (WordSpace I →L[ℂ] WordSpace I)), mul_zero]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
/-- Actual amplified mixed OU as products of the genuine real residual-prefix terms. -/
theorem actualFamilyWordOUMatrix_mixed_prefix_terms (e : I → H) (he : Orthonormal ℂ e)
    (t : ℝ) (ht : 0 ≤ t) (C D : Matrix ν ν ℂ) (u v : List I) :
    actualFamilyWordOUMatrix e he t ht
      (matrixClosedWickTerm C u * star (matrixClosedWickTerm D v)) =
      mixedMatrixPrefixTerm C u (Real.exp (-t)) [] *
        star (mixedMatrixPrefixTerm D v (Real.exp (-t)) []) +
      (1 - (Real.exp (-t) : ℂ) ^ 2) • ∑ s ∈ u.tails.toFinset.erase [],
        mixedMatrixPrefixTerm C u (Real.exp (-t)) s *
          star (mixedMatrixPrefixTerm D v (Real.exp (-t)) s) := by
  rw [actualFamilyWordOUMatrix_mixed_suffix_Gram]
  have hnil : mixedMatrixPrefixTerm C u (Real.exp (-t)) [] *
      star (mixedMatrixPrefixTerm D v (Real.exp (-t)) []) =
      (Real.exp (-t) : ℂ) ^ (u.length + v.length) •
        (matrixWickTerm C u * star (matrixWickTerm D v)) := by
    rw [mixedMatrixPrefixTerm_nil, mixedMatrixPrefixTerm_nil]
    exact real_scaled_mul_star_power (Real.exp (-t)) u.length v.length
      (matrixWickTerm C u) (matrixWickTerm D v)
  rw [hnil]
  congr 1
  apply congrArg (fun z => (1 - (Real.exp (-t) : ℂ) ^ 2) • z)
  apply Finset.sum_congr rfl
  intro s hs
  have hu : s.IsSuffix u := (List.mem_tails _ _).mp
    (List.mem_toFinset.mp (Finset.mem_erase.mp hs).2)
  exact (mixedMatrixPrefixTerm_mul_star C D u v s (Real.exp (-t)) hu).symm

/-- Actual pairwise expansion over any finite common support containing the first word's tails. -/
theorem actualFamilyWordOUMatrix_mixed_prefix_support (e : I → H) (he : Orthonormal ℂ e)
    (t : ℝ) (ht : 0 ≤ t) (C D : Matrix ν ν ℂ) (u v : List I)
    (T : Finset (List I)) (hT : u.tails.toFinset ⊆ T) :
    actualFamilyWordOUMatrix e he t ht
      (matrixClosedWickTerm C u * star (matrixClosedWickTerm D v)) =
      mixedMatrixPrefixTerm C u (Real.exp (-t)) [] *
        star (mixedMatrixPrefixTerm D v (Real.exp (-t)) []) +
      (1 - (Real.exp (-t) : ℂ) ^ 2) • ∑ s ∈ T.erase [],
        mixedMatrixPrefixTerm C u (Real.exp (-t)) s *
          star (mixedMatrixPrefixTerm D v (Real.exp (-t)) s) := by
  rw [actualFamilyWordOUMatrix_mixed_prefix_terms]
  congr 1
  apply congrArg (fun z => (1 - (Real.exp (-t) : ℂ) ^ 2) • z)
  apply Finset.sum_subset (Finset.erase_subset_erase [] hT)
  intro s hs hn
  have hne := (Finset.mem_erase.mp hs).1
  have hu : ¬ s.IsSuffix u := by
    intro hu
    exact hn (Finset.mem_erase.mpr ⟨hne, List.mem_toFinset.mpr ((List.mem_tails _ _).mpr hu)⟩)
  simp only [mixedMatrixPrefixTerm, hu, ite_false, zero_mul]

end FreeProbability.Fock

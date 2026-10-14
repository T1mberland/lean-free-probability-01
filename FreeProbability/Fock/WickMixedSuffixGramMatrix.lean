import FreeProbability.Fock.WickMixedSuffixGramWeightedSums

/-! # Actual ordered matrix mixed Wick product expansion -/
noncomputable section
open scoped Classical BigOperators
namespace FreeProbability.Fock
variable {I H ν : Type*} [Fintype ν] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The genuine amplified family OU map has the full mixed pairwise suffix expansion. -/
theorem actualFamilyWordOUMatrix_mixed_suffix_Gram (e : I → H) (he : Orthonormal ℂ e)
    (t : ℝ) (ht : 0 ≤ t) (C D : Matrix ν ν ℂ) (u v : List I) :
    actualFamilyWordOUMatrix e he t ht
      (matrixClosedWickTerm C u * star (matrixClosedWickTerm D v)) =
      (Real.exp (-t) : ℂ) ^ (u.length + v.length) •
        (matrixWickTerm C u * star (matrixWickTerm D v)) +
      (1 - (Real.exp (-t) : ℂ) ^ 2) • ∑ s ∈ u.tails.toFinset.erase [],
        if s.IsSuffix v then (Real.exp (-t) : ℂ) ^ (u.length + v.length - 2 * s.length) •
          (matrixWickTerm C (u.take (u.length - s.length)) *
            star (matrixWickTerm D (v.take (v.length - s.length)))) else 0 := by
  rw [matrixClosedWickTerm_mul_star]
  have hm : actualFamilyWordOUMatrix e he t ht
      (CStarMatrix.ofMatrix (fun i j => (C * D.conjTranspose) i j •
        (suffixGramClosedWick u * star (suffixGramClosedWick v)))) =
      matrixCoefficientOperator (C * D.conjTranspose)
        (actualFamilyWordOU e he t ht (suffixGramClosedWick u * star (suffixGramClosedWick v))) := by
    apply CStarMatrix.ext
    intro i j
    change actualFamilyWordOU e he t ht ((C * D.conjTranspose) i j • _) = _
    exact map_smul (actualFamilyWordOU e he t ht) _ _
  rw [hm, actualFamilyWordOU_mixed_suffix_Gram e he t ht u v]
  simp only [map_add, map_sum, map_smul, apply_ite, map_zero,
    ← matrixWickTerm_mul_star_coefficient]

end FreeProbability.Fock

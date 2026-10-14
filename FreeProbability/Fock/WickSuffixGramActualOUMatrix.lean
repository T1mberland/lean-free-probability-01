import FreeProbability.Fock.WickSuffixGramActualOUProduct

/-! # Actual matrix amplification of prescribed-family OU on homogeneous Wick products -/
noncomputable section
open scoped Classical BigOperators
namespace FreeProbability.Fock
variable {I H ν : Type*} [Fintype ν] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Genuine entrywise amplification of the transported actual OU linear map. -/
def actualFamilyWordOUMatrix (e : I → H) (he : Orthonormal ℂ e) (t : ℝ) (ht : 0 ≤ t) :
    CStarMatrix ν ν (closedSemicircularAlgebra I) →ₗ[ℂ]
      CStarMatrix ν ν (WordSpace I →L[ℂ] WordSpace I) :=
  CStarMatrix.mapₗ (actualFamilyWordOU e he t ht)

/-- Actual coefficient term inside the word norm closure. -/
def matrixClosedWickTerm (C : Matrix ν ν ℂ) (w : List I) :
    CStarMatrix ν ν (closedSemicircularAlgebra I) :=
  CStarMatrix.ofMatrix (fun i j => C i j • suffixGramClosedWick w)

/-- Ordered matrix product inside the actual closed word algebra. -/
theorem matrixClosedWickTerm_mul_star (C D : Matrix ν ν ℂ) (u v : List I) :
    matrixClosedWickTerm C u * star (matrixClosedWickTerm D v) =
      CStarMatrix.ofMatrix (fun i j => (C * D.conjTranspose) i j •
        (suffixGramClosedWick u * star (suffixGramClosedWick v))) := by
  apply CStarMatrix.ofMatrix.symm.injective
  funext i j
  change (∑ k, (C i k • suffixGramClosedWick u) * star (D j k • suffixGramClosedWick v)) =
    (∑ k, C i k * star (D j k)) • (suffixGramClosedWick u * star (suffixGramClosedWick v))
  simp only [star_smul, smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm]
  exact Finset.sum_smul.symm

/-- The true amplified family OU map agrees with the literal matrix contractions. -/
theorem actualFamilyWordOUMatrix_Wick_mul_star (e : I → H) (he : Orthonormal ℂ e)
    (t : ℝ) (ht : 0 ≤ t) (C D : Matrix ν ν ℂ) (u v : List I)
    (hl : u.length = v.length) :
    actualFamilyWordOUMatrix e he t ht
      (matrixClosedWickTerm C u * star (matrixClosedWickTerm D v)) =
      ∑ k ∈ Finset.range (u.length + 1), (Real.exp (-t) : ℂ) ^ (2 * k) •
        (if u.drop k = v.drop k then
          matrixWickTerm (C * D.conjTranspose) (u.take k ++ (v.take k).reverse) else 0) := by
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
  rw [hm, actualFamilyWordOU_Wick_mul_star e he t ht u v hl]
  simp only [map_sum, map_smul, apply_ite, map_zero, matrixCoefficientOperator_wick]

end FreeProbability.Fock

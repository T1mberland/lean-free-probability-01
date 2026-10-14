import FreeProbability.Fock.WickMixedSuffixGramFinite

/-! # Literal identification with the original finite-support suffix Gram construction -/
noncomputable section
open scoped Classical
namespace FreeProbability.Fock
variable {I ν : Type*} [Fintype ν]

omit [Fintype ν] in
/-- The real weighted prefix amplitudes are precisely the original finite-support amplitudes. -/
theorem mixedMatrixSuffixAmplitude_finsupp (C : List I →₀ Matrix ν ν ℂ) (α : ℝ) (s : List I) :
    mixedMatrixSuffixAmplitude C.support C α s = matrixSuffixAmplitude C α s := by
  simp only [mixedMatrixSuffixAmplitude, mixedMatrixPrefixTerm, matrixSuffixAmplitude,
    Complex.ofReal_pow]

omit [Fintype ν] in
/-- Both constructions use exactly the same actual finite union of terminal words. -/
theorem mixedMatrixSuffixSupport_finsupp (C : List I →₀ Matrix ν ν ℂ) :
    mixedMatrixSuffixSupport C.support = matrixWickSuffixSupport C := rfl

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
/-- The original mixed finite-support Gram candidate is the genuine amplified family OU image.
This discharges its previously explicit equality obligation, with actual real damping. -/
theorem actualFamilyWordOUMatrix_finsupp_suffixGram (e : I → H) (he : Orthonormal ℂ e)
    (t : ℝ) (ht : 0 ≤ t) (C : List I →₀ Matrix ν ν ℂ) :
    actualFamilyWordOUMatrix e he t ht
      (matrixClosedWickAmplitude C.support C * star (matrixClosedWickAmplitude C.support C)) =
      matrixSuffixGram C (Real.exp (-t)) := by
  rw [actualFamilyWordOUMatrix_mixed_amplitude_Gram]
  simp only [mixedMatrixSuffixAmplitude_finsupp, mixedMatrixSuffixSupport_finsupp,
    matrixSuffixGram, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow]

end FreeProbability.Fock

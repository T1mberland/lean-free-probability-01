import FreeProbability.Fock.WickSuffixGramAmplitude

/-! # Exact ordered coefficient multiplication in actual Wick operator matrices -/
noncomputable section
open scoped Classical BigOperators
namespace FreeProbability.Fock
variable {I ν : Type*} [Fintype ν]

/-- Matrix coefficient order in a Wick amplitude product is exactly `C Dᴴ`.
The equality is in the genuine C-star matrix algebra of completed-space operators. -/
theorem matrixWickTerm_mul_star (C D : Matrix ν ν ℂ) (u v : List I) :
    matrixWickTerm C u * star (matrixWickTerm D v) =
      CStarMatrix.ofMatrix (fun i j => (C * D.conjTranspose) i j •
        (wick u * star (wick v))) := by
  apply CStarMatrix.ofMatrix.symm.injective
  funext i j
  change (∑ k, (C i k • wick u) * star (D j k • wick v)) =
    (∑ k, C i k * star (D j k)) • (wick u * star (wick v))
  simp only [star_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
  simp only [mul_comm]
  exact Finset.sum_smul.symm

end FreeProbability.Fock

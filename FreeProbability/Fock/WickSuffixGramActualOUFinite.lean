import FreeProbability.Fock.WickSuffixGramActualOUMatrix

/-! # Actual amplified OU positive Gram decomposition for finite homogeneous amplitudes -/
noncomputable section
open scoped Classical BigOperators
namespace FreeProbability.Fock
variable {I H ν : Type*} [Fintype ν] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A genuine finite matrix Wick amplitude in the canonical word norm closure. -/
def matrixClosedWickAmplitude (S : Finset (List I)) (C : List I → Matrix ν ν ℂ) :
    CStarMatrix ν ν (closedSemicircularAlgebra I) :=
  ∑ w ∈ S, matrixClosedWickTerm (C w) w

omit [Fintype ν] in
/-- Exact connection of the amplified map with the actual native double-commutant CP map. -/
theorem actualFamilyWordOUMatrix_entry (e : I → H) (he : Orthonormal ℂ e)
    (t : ℝ) (ht : 0 ≤ t) (M : CStarMatrix ν ν (closedSemicircularAlgebra I)) (i j : ν) :
    actualFamilyWordOUMatrix e he t ht M i j =
      familyWordRepresentation e he (ouVonNeumannTimeCP e t ht
        (ouCyclicNativeInclusion e ((familyNativeWordEquiv e he).symm (M i j)))) := rfl

/-- The true amplified OU image of the actual homogeneous amplitude star-square
is precisely the previously verified literal contraction polynomial. -/
theorem actualFamilyWordOUMatrix_amplitude_product (e : I → H) (he : Orthonormal ℂ e)
    (t : ℝ) (ht : 0 ≤ t) (S : Finset (List I)) (C : List I → Matrix ν ν ℂ)
    (n : ℕ) (hn : ∀ w ∈ S, w.length = n) :
    actualFamilyWordOUMatrix e he t ht
      (matrixClosedWickAmplitude S C * star (matrixClosedWickAmplitude S C)) =
        matrixHomogeneousDampedProduct S C (Real.exp (-t) : ℂ) n := by
  unfold matrixClosedWickAmplitude matrixHomogeneousDampedProduct
  rw [star_sum S (fun w => matrixClosedWickTerm (C w) w), Finset.sum_mul]
  simp_rw [Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  simpa only [hn u hu] using actualFamilyWordOUMatrix_Wick_mul_star e he t ht
    (C u) (C v) u v ((hn u hu).trans (hn v hv).symm)

/-- Actual homogeneous positive suffix decomposition for any prescribed ON family,
at every finite canonical matrix level and every nonnegative time. -/
theorem actualFamilyWordOUMatrix_amplitude_Gram (e : I → H) (he : Orthonormal ℂ e)
    (t : ℝ) (ht : 0 ≤ t) (S : Finset (List I)) (C : List I → Matrix ν ν ℂ)
    (n : ℕ) (hn : ∀ w ∈ S, w.length = n) :
    actualFamilyWordOUMatrix e he t ht
      (matrixClosedWickAmplitude S C * star (matrixClosedWickAmplitude S C)) =
      (Real.exp (-t) : ℂ) ^ (2 * n) • matrixCutGram S C n +
      (1 - (Real.exp (-t) : ℂ) ^ 2) • ∑ h ∈ Finset.range n,
        (Real.exp (-t) : ℂ) ^ (2 * h) • matrixCutGram S C h := by
  rw [actualFamilyWordOUMatrix_amplitude_product e he t ht S C n hn]
  exact matrixHomogeneousDampedProduct_Gram S C n hn _

/-- Genuine full canonical-matrix positivity of the actual amplified OU output. -/
theorem actualFamilyWordOUMatrix_amplitude_nonneg (e : I → H) (he : Orthonormal ℂ e)
    (t : ℝ) (ht : 0 ≤ t) (S : Finset (List I)) (C : List I → Matrix ν ν ℂ)
    (n : ℕ) (hn : ∀ w ∈ S, w.length = n) :
    0 ≤ actualFamilyWordOUMatrix e he t ht
      (matrixClosedWickAmplitude S C * star (matrixClosedWickAmplitude S C)) := by
  rw [actualFamilyWordOUMatrix_amplitude_product e he t ht S C n hn]
  apply matrixHomogeneousDampedProduct_nonneg S C n hn (Real.exp_pos _).le
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)

end FreeProbability.Fock

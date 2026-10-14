import FreeProbability.Fock.WickMixedSuffixGramPrefixTerms

/-! # Actual positive suffix Gram decomposition of every finite mixed matrix Wick amplitude -/
noncomputable section
open scoped Classical BigOperators ComplexOrder
namespace FreeProbability.Fock
variable {I ν : Type*} [Fintype ν]

/-- Actual finite union of terminal words, independent of alphabet cardinality. -/
def mixedMatrixSuffixSupport (S : Finset (List I)) : Finset (List I) :=
  S.biUnion (fun u => u.tails.toFinset)

/-- Actual finite residual-prefix amplitude, allowing arbitrary mixed word degrees. -/
def mixedMatrixSuffixAmplitude (S : Finset (List I)) (C : List I → Matrix ν ν ℂ)
    (α : ℝ) (s : List I) : CStarMatrix ν ν (WordSpace I →L[ℂ] WordSpace I) :=
  ∑ u ∈ S, mixedMatrixPrefixTerm (C u) u α s

/-- Exact ordered expansion of each actual finite residual-amplitude square. -/
theorem mixedMatrixSuffixAmplitude_mul_star (S : Finset (List I))
    (C : List I → Matrix ν ν ℂ) (α : ℝ) (s : List I) :
    mixedMatrixSuffixAmplitude S C α s * star (mixedMatrixSuffixAmplitude S C α s) =
      ∑ u ∈ S, ∑ v ∈ S, mixedMatrixPrefixTerm (C u) u α s *
        star (mixedMatrixPrefixTerm (C v) v α s) := by
  unfold mixedMatrixSuffixAmplitude
  rw [star_sum S (fun u => mixedMatrixPrefixTerm (C u) u α s), Finset.sum_mul]
  simp_rw [Finset.mul_sum]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
/-- Full actual amplified OU suffix Gram identity for arbitrary finite mixed amplitudes.
The coefficients retain their true matrix multiplication order and damping is real. -/
theorem actualFamilyWordOUMatrix_mixed_amplitude_Gram (e : I → H) (he : Orthonormal ℂ e)
    (t : ℝ) (ht : 0 ≤ t) (S : Finset (List I)) (C : List I → Matrix ν ν ℂ) :
    actualFamilyWordOUMatrix e he t ht
      (matrixClosedWickAmplitude S C * star (matrixClosedWickAmplitude S C)) =
      mixedMatrixSuffixAmplitude S C (Real.exp (-t)) [] *
        star (mixedMatrixSuffixAmplitude S C (Real.exp (-t)) []) +
      (1 - (Real.exp (-t) : ℂ) ^ 2) • ∑ s ∈ (mixedMatrixSuffixSupport S).erase [],
        mixedMatrixSuffixAmplitude S C (Real.exp (-t)) s *
          star (mixedMatrixSuffixAmplitude S C (Real.exp (-t)) s) := by
  let T := mixedMatrixSuffixSupport S
  have hT : ∀ u ∈ S, u.tails.toFinset ⊆ T := by
    intro u hu s hs
    exact Finset.mem_biUnion.mpr ⟨u, hu, hs⟩
  unfold matrixClosedWickAmplitude
  rw [star_sum S (fun u => matrixClosedWickTerm (C u) u), Finset.sum_mul]
  simp_rw [Finset.mul_sum, map_sum]
  trans ∑ u ∈ S, ∑ v ∈ S,
    (mixedMatrixPrefixTerm (C u) u (Real.exp (-t)) [] *
        star (mixedMatrixPrefixTerm (C v) v (Real.exp (-t)) []) +
      (1 - (Real.exp (-t) : ℂ) ^ 2) • ∑ s ∈ T.erase [],
        mixedMatrixPrefixTerm (C u) u (Real.exp (-t)) s *
          star (mixedMatrixPrefixTerm (C v) v (Real.exp (-t)) s))
  · apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    exact actualFamilyWordOUMatrix_mixed_prefix_support e he t ht (C u) (C v) u v T (hT u hu)
  · simp only [Finset.sum_add_distrib, ← Finset.smul_sum]
    rw [mixedMatrixSuffixAmplitude_mul_star]
    congr 1
    apply congrArg (fun z => (1 - (Real.exp (-t) : ℂ) ^ 2) • z)
    conv_lhs =>
      arg 2
      ext u
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s hs
    exact (mixedMatrixSuffixAmplitude_mul_star S C (Real.exp (-t)) s).symm

/-- Full canonical matrix positivity of the actual mixed-amplitude OU output. -/
theorem actualFamilyWordOUMatrix_mixed_amplitude_nonneg (e : I → H) (he : Orthonormal ℂ e)
    (t : ℝ) (ht : 0 ≤ t) (S : Finset (List I)) (C : List I → Matrix ν ν ℂ) :
    0 ≤ actualFamilyWordOUMatrix e he t ht
      (matrixClosedWickAmplitude S C * star (matrixClosedWickAmplitude S C)) := by
  apply (hilbertMatrixStarAlgEquiv_nonneg_iff _).mp
  rw [actualFamilyWordOUMatrix_mixed_amplitude_Gram]
  simp only [map_add, map_smul, map_sum, map_mul, map_star]
  apply add_nonneg (mul_star_self_nonneg _)
  apply smul_nonneg
  · have hα0 : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
    have hα1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
    have hsq : Real.exp (-t) ^ 2 ≤ 1 := by nlinarith
    have hh := (RCLike.ofReal_nonneg (K := ℂ)).mpr (sub_nonneg.mpr hsq)
    change 0 ≤ ((1 - Real.exp (-t) ^ 2 : ℝ) : ℂ) at hh
    simpa only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow] using hh
  · exact Finset.sum_nonneg (fun _ _ => mul_star_self_nonneg _)

end FreeProbability.Fock

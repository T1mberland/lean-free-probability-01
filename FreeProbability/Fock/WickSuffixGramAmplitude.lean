import FreeProbability.Fock.WickSuffixGramWeights
import FreeProbability.Fock.SecondQuantizationCompressionMatrix
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Data.List.Infix

/-! # Finite actual matrix Wick amplitudes and canonical positive suffix Gram sums

The positive candidate is constructed in the genuine finite matrix operator cone.
Its identification with the OU image is a separate remaining identity.
-/
noncomputable section
open scoped Classical BigOperators ComplexOrder
namespace FreeProbability.Fock
variable {I ν : Type*} [Fintype ν]


/-- A matrix coefficient multiplying an actual Wick operator entry by entry. -/
def matrixWickTerm (C : Matrix ν ν ℂ) (w : List I) :
    CStarMatrix ν ν (WordSpace I →L[ℂ] WordSpace I) :=
  CStarMatrix.ofMatrix (fun i j => C i j • wick w)

/-- The finite residual-prefix amplitude attached to a fixed common suffix. -/
def matrixSuffixAmplitude (C : List I →₀ Matrix ν ν ℂ) (α : ℝ) (s : List I) :
    CStarMatrix ν ν (WordSpace I →L[ℂ] WordSpace I) :=
  ∑ w ∈ C.support, if s.IsSuffix w then
    ((α ^ (w.length - s.length) : ℝ) : ℂ) •
      matrixWickTerm (C w) (w.take (w.length - s.length)) else 0

/-- The genuine finite suffix support, with no finite-alphabet assumption. -/
def matrixWickSuffixSupport (C : List I →₀ Matrix ν ν ℂ) : Finset (List I) :=
  C.support.biUnion (fun w => w.tails.toFinset)

omit [Fintype ν] in
@[simp] theorem matrixSuffixAmplitude_nil (C : List I →₀ Matrix ν ν ℂ) (α : ℝ) :
    matrixSuffixAmplitude C α [] = ∑ w ∈ C.support,
      ((α ^ w.length : ℝ) : ℂ) • matrixWickTerm (C w) w := by
  simp [matrixSuffixAmplitude]

omit [Fintype ν] in
/-- Outside the genuine finite suffix support the residual amplitude vanishes. -/
theorem matrixSuffixAmplitude_eq_zero (C : List I →₀ Matrix ν ν ℂ) (α : ℝ)
    (s : List I) (hs : s ∉ matrixWickSuffixSupport C) : matrixSuffixAmplitude C α s = 0 := by
  apply Finset.sum_eq_zero
  intro w hw
  have hn : ¬ s.IsSuffix w := by
    intro h
    apply hs
    apply Finset.mem_biUnion.mpr
    exact ⟨w, hw, List.mem_toFinset.mpr ((List.mem_tails s w).mpr h)⟩
  simp [hn]

/-- The positive suffix Gram candidate; equality with actual OU is not presumed. -/
def matrixSuffixGram (C : List I →₀ Matrix ν ν ℂ) (α : ℝ) :
    CStarMatrix ν ν (WordSpace I →L[ℂ] WordSpace I) :=
  matrixSuffixAmplitude C α [] * star (matrixSuffixAmplitude C α []) +
    ((1 - α ^ 2 : ℝ) : ℂ) • ∑ s ∈ (matrixWickSuffixSupport C).erase [],
      matrixSuffixAmplitude C α s * star (matrixSuffixAmplitude C α s)

/-- Full canonical matrix positivity, not entrywise or product-vector positivity. -/
theorem matrixSuffixGram_nonneg (C : List I →₀ Matrix ν ν ℂ) {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) : 0 ≤ matrixSuffixGram C α := by
  apply (hilbertMatrixStarAlgEquiv_nonneg_iff _).mp
  simp only [matrixSuffixGram, map_add, map_smul, map_sum, map_mul, map_star]
  apply add_nonneg (mul_star_self_nonneg _)
  apply smul_nonneg
  · have hs : α ^ 2 ≤ 1 := by nlinarith
    exact (RCLike.ofReal_nonneg (K := ℂ)).mpr (sub_nonneg.mpr hs)
  · exact Finset.sum_nonneg (fun s _ => mul_star_self_nonneg _)

end FreeProbability.Fock

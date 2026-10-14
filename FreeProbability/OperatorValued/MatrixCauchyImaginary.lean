import FreeProbability.OperatorValued.MatrixPencilResolvent
import FreeProbability.OperatorValued.MatrixStatePositivity

/-! # Genuine matrix resolvent imaginary-part identity and positivity -/

noncomputable section
open scoped Classical ComplexOrder
open Matrix
namespace FreeProbability

variable {A n : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

omit [StarModule ℂ A] in
/-- Entrywise star preservation respects the full conjugate transpose. -/
theorem matrixExpectation_conjTranspose (φ : StarProbabilitySpace A) (T : Matrix n n A) :
    matrixExpectation φ.toProbabilitySpace Tᴴ = (matrixExpectation φ.toProbabilitySpace T)ᴴ := by
  apply Matrix.ext
  intro r c
  exact φ.map_star (T c r)

/-- Negative Hermitian imaginary part of a complex matrix. -/
def matrixNegativeImaginaryPart (M : Matrix n n ℂ) : Matrix n n ℂ :=
  (Complex.I / 2) • (M - Mᴴ)

namespace Fock
variable {I : Type*} [Fintype I] [Fintype n] [DecidableEq n]
local instance : PartialOrder (WordSpace I →L[ℂ] WordSpace I) := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing (WordSpace I →L[ℂ] WordSpace I) :=
  CStarAlgebra.spectralOrderedRing _

/-- Exact imaginary-part identity for the genuine affine pencil Cauchy transform. -/
theorem operatorMatrixPencilCauchy_negativeImaginaryPart (C₀ : Matrix n n ℂ)
    (C : I → Matrix n n ℂ) (hC₀ : C₀.IsHermitian) (hC : ∀ i, (C i).IsHermitian)
    (z : ℂ) (hz : z ∈ resolventSet ℂ (operatorMatrixPencil C₀ C)) :
    matrixNegativeImaginaryPart (operatorMatrixPencilCauchy C₀ C z) =
      (z.im : ℂ) • matrixExpectation (vacuumState I).toProbabilitySpace
        (CStarMatrix.ofMatrix.symm (resolvent (operatorMatrixPencil C₀ C) z) *
          (CStarMatrix.ofMatrix.symm (resolvent (operatorMatrixPencil C₀ C) z))ᴴ) := by
  let H := operatorMatrixPencil C₀ C
  have hH : IsSelfAdjoint H := operatorMatrixPencil_isSelfAdjoint C₀ C hC₀ hC
  have hs : star (algebraMap ℂ _ z - H) - (algebraMap ℂ _ z - H) =
      (star z - z) • (1 : CStarMatrix n n (WordSpace I →L[ℂ] WordSpace I)) := by
    rw [Algebra.algebraMap_eq_smul_one]
    rw [star_sub (z • (1 : CStarMatrix n n (WordSpace I →L[ℂ] WordSpace I))) H]
    rw [star_smul z (1 : CStarMatrix n n (WordSpace I →L[ℂ] WordSpace I)), star_one, hH.star_eq,
      sub_smul (star z) z (1 : CStarMatrix n n (WordSpace I →L[ℂ] WordSpace I))]
    abel
  have hr := StarProbabilitySpace.inverse_sub_star_inverse (algebraMap ℂ _ z - H) hz
  rw [hs] at hr
  simp only [mul_smul_comm, mul_one, smul_mul_assoc] at hr
  change CStarMatrix.ofMatrix
    (CStarMatrix.ofMatrix.symm (resolvent H z) - (CStarMatrix.ofMatrix.symm (resolvent H z))ᴴ) =
      CStarMatrix.ofMatrix ((star z - z) •
        (CStarMatrix.ofMatrix.symm (resolvent H z) * (CStarMatrix.ofMatrix.symm (resolvent H z))ᴴ)) at hr
  have he := congrArg (matrixExpectation (vacuumState I).toProbabilitySpace)
    (CStarMatrix.ofMatrix.injective hr)
  rw [map_sub, matrixExpectation_conjTranspose, map_smul] at he
  have hc : (Complex.I / 2) * (star z - z) = (z.im : ℂ) := by
    apply Complex.ext
    · simp [Complex.mul_re]
      ring
    · simp [Complex.mul_im]
  unfold matrixNegativeImaginaryPart operatorMatrixPencilCauchy
  rw [he, smul_smul, hc]

/-- The actual matrix Cauchy transform has nonpositive Hermitian imaginary part
throughout the upper half-plane. This statement is positive semidefiniteness. -/
theorem operatorMatrixPencilCauchy_negativeImaginaryPart_posSemidef (C₀ : Matrix n n ℂ)
    (C : I → Matrix n n ℂ) (hC₀ : C₀.IsHermitian) (hC : ∀ i, (C i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im) :
    (matrixNegativeImaginaryPart (operatorMatrixPencilCauchy C₀ C z)).PosSemidef := by
  have hr := StarProbabilitySpace.selfAdjoint_mem_resolventSet_of_im_ne_zero (operatorMatrixPencil C₀ C)
    (operatorMatrixPencil_isSelfAdjoint C₀ C hC₀ hC) z hz.ne'
  rw [operatorMatrixPencilCauchy_negativeImaginaryPart C₀ C hC₀ hC z hr]
  have hp := matrixExpectation_gram_posSemidef (vacuumState I)
    (CStarMatrix.ofMatrix.symm (resolvent (operatorMatrixPencil C₀ C) z))ᴴ
  simp only [Matrix.conjTranspose_conjTranspose] at hp
  exact hp.smul (Complex.zero_le_real.mpr hz.le)

end Fock
end FreeProbability

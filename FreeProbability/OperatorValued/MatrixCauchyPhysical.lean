import FreeProbability.OperatorValued.MatrixVacuumGram

/-! # Strict upper-half-plane sign for the actual affine matrix Cauchy transform

The sign is established for the genuine inverse, not imposed as an assumption
on a solution of Dyson's equation. Uniqueness of the analytic branch is separate.
-/

noncomputable section
open scoped Classical ComplexOrder
open Matrix
namespace FreeProbability.Fock

variable {I n : Type*} [Fintype I] [Fintype n] [DecidableEq n]
local instance : PartialOrder (WordSpace I →L[ℂ] WordSpace I) := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing (WordSpace I →L[ℂ] WordSpace I) :=
  CStarAlgebra.spectralOrderedRing _

/-- Gram expectation of the actual inverse is strictly positive at every
resolvent point; the vacuum state need not be faithful on all bounded operators. -/
theorem operatorMatrixPencil_resolvent_gram_posDef (C₀ : Matrix n n ℂ)
    (C : I → Matrix n n ℂ) (z : ℂ) (hz : z ∈ resolventSet ℂ (operatorMatrixPencil C₀ C)) :
    (matrixExpectation (vacuumState I).toProbabilitySpace
      (CStarMatrix.ofMatrix.symm (resolvent (operatorMatrixPencil C₀ C) z) *
        (CStarMatrix.ofMatrix.symm (resolvent (operatorMatrixPencil C₀ C) z))ᴴ)).PosDef := by
  have hR : IsUnit (CStarMatrix.ofMatrix.symm (resolvent (operatorMatrixPencil C₀ C) z)) := by
    exact hz.ringInverse.map ((CStarMatrix.ofMatrixRingEquiv (n := n) (A := WordSpace I →L[ℂ] WordSpace I)).symm.toMonoidHom)
  simpa only [Matrix.conjTranspose_conjTranspose] using
    matrixVacuumGram_posDef (CStarMatrix.ofMatrix.symm (resolvent (operatorMatrixPencil C₀ C) z))ᴴ
      ((Matrix.isUnit_conjTranspose (CStarMatrix.ofMatrix.symm (resolvent (operatorMatrixPencil C₀ C) z))).mpr hR)

/-- The actual affine matrix Cauchy transform has strictly negative Hermitian
imaginary part at every upper-half-plane argument. -/
theorem operatorMatrixPencilCauchy_negativeImaginaryPart_posDef (C₀ : Matrix n n ℂ)
    (C : I → Matrix n n ℂ) (hC₀ : C₀.IsHermitian) (hC : ∀ i, (C i).IsHermitian)
    (z : ℂ) (hz : 0 < z.im) :
    (matrixNegativeImaginaryPart (operatorMatrixPencilCauchy C₀ C z)).PosDef := by
  have hr := StarProbabilitySpace.selfAdjoint_mem_resolventSet_of_im_ne_zero (operatorMatrixPencil C₀ C)
    (operatorMatrixPencil_isSelfAdjoint C₀ C hC₀ hC) z hz.ne'
  rw [operatorMatrixPencilCauchy_negativeImaginaryPart C₀ C hC₀ hC z hr]
  exact (operatorMatrixPencil_resolvent_gram_posDef C₀ C z hr).smul
    (Complex.zero_lt_real.mpr hz)

end FreeProbability.Fock

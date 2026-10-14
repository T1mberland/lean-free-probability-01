import FreeProbability.OperatorValued.MatrixArgumentDyson

/-! # Actual affine Fock matrix pencil resolvent Dyson equation -/

noncomputable section
open scoped Classical
namespace FreeProbability.Fock

variable {I n : Type*} [Fintype I] [Fintype n] [DecidableEq n]

local instance : PartialOrder (WordSpace I →L[ℂ] WordSpace I) := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing (WordSpace I →L[ℂ] WordSpace I) :=
  CStarAlgebra.spectralOrderedRing _

/-- The genuine affine matrix pencil, with the actual C-star matrix norm. -/
def operatorMatrixPencil (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ) :
    CStarMatrix n n (WordSpace I →L[ℂ] WordSpace I) :=
  CStarMatrix.ofMatrix (scalarMatrixEmbedding C₀ + matrixLinearCombination semicircular C)

/-- The entrywise vacuum average of the actual affine pencil inverse. -/
def operatorMatrixPencilCauchy (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ) (z : ℂ) : Matrix n n ℂ :=
  matrixExpectation (vacuumState I).toProbabilitySpace
    (CStarMatrix.ofMatrix.symm (resolvent (operatorMatrixPencil C₀ C) z))

/-- Scalar affine pencil resolvents are literal matrix-argument inverses. -/
theorem operatorMatrixDifference_pencil (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ) (z : ℂ) :
    operatorMatrixDifference C (z • (1 : Matrix n n ℂ) - C₀) =
      algebraMap ℂ _ z - operatorMatrixPencil C₀ C := by
  simp only [Algebra.algebraMap_eq_smul_one]
  apply CStarMatrix.ofMatrix.injective.eq_iff.mpr
  change scalarMatrixEmbedding (z • (1 : Matrix n n ℂ) - C₀) -
      matrixLinearCombination semicircular C =
    z • (1 : Matrix n n (WordSpace I →L[ℂ] WordSpace I)) -
      (scalarMatrixEmbedding C₀ + matrixLinearCombination semicircular C)
  rw [map_sub, map_smul, map_one]
  abel

/-- The two Cauchy-transform definitions evaluate the same true inverse. -/
theorem operatorMatrixArgumentCauchy_pencil (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ) (z : ℂ) :
    operatorMatrixArgumentCauchy C (z • (1 : Matrix n n ℂ) - C₀) =
      operatorMatrixPencilCauchy C₀ C z := by
  unfold operatorMatrixArgumentCauchy operatorMatrixArgumentResolvent
  rw [operatorMatrixDifference_pencil]
  rfl

/-- Actual affine pencil Dyson identity throughout its genuine resolvent set. -/
theorem operatorMatrixPencilCauchy_dyson (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ) (z : ℂ)
    (hz : z ∈ resolventSet ℂ (operatorMatrixPencil C₀ C)) :
    (z • (1 : Matrix n n ℂ) - C₀ - matrixCovariance C (operatorMatrixPencilCauchy C₀ C z)) *
      operatorMatrixPencilCauchy C₀ C z = 1 := by
  have hunit : IsUnit (operatorMatrixDifference C (z • (1 : Matrix n n ℂ) - C₀)) := by
    rw [operatorMatrixDifference_pencil]
    exact hz
  simpa only [operatorMatrixArgumentCauchy_pencil] using
    operatorMatrixArgumentCauchy_dyson C (z • (1 : Matrix n n ℂ) - C₀) hunit

/-- Inverse Dyson form for the actual affine matrix pencil Cauchy transform. -/
theorem operatorMatrixPencilCauchy_inverse_dyson (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ) (z : ℂ)
    (hz : z ∈ resolventSet ℂ (operatorMatrixPencil C₀ C)) :
    (operatorMatrixPencilCauchy C₀ C z)⁻¹ = z • (1 : Matrix n n ℂ) - C₀ -
      matrixCovariance C (operatorMatrixPencilCauchy C₀ C z) :=
  Matrix.inv_eq_left_inv (operatorMatrixPencilCauchy_dyson C₀ C z hz)

/-- Hermitian deterministic drift and coefficients give a true self-adjoint pencil. -/
theorem operatorMatrixPencil_isSelfAdjoint (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ)
    (hC₀ : C₀.IsHermitian) (hC : ∀ i, (C i).IsHermitian) : IsSelfAdjoint (operatorMatrixPencil C₀ C) := by
  change CStarMatrix.ofMatrix (scalarMatrixEmbedding C₀ + matrixLinearCombination semicircular C).conjTranspose =
    CStarMatrix.ofMatrix (scalarMatrixEmbedding C₀ + matrixLinearCombination semicircular C)
  apply congrArg CStarMatrix.ofMatrix
  apply Matrix.IsHermitian.add
  · apply Matrix.IsHermitian.ext
    intro r c
    simp only [scalarMatrixEmbedding_apply, Algebra.algebraMap_eq_smul_one, star_smul, star_one, hC₀.apply]
  · exact matrixLinearCombination_isHermitian semicircular C
      (fun i => (isSelfAdjoint_semicircular i).star_eq) hC

/-- Hermitian affine pencils satisfy actual inverse Dyson at every nonreal argument. -/
theorem operatorMatrixPencilCauchy_inverse_dyson_nonreal (C₀ : Matrix n n ℂ)
    (C : I → Matrix n n ℂ) (hC₀ : C₀.IsHermitian) (hC : ∀ i, (C i).IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) :
    (operatorMatrixPencilCauchy C₀ C z)⁻¹ = z • (1 : Matrix n n ℂ) - C₀ -
      matrixCovariance C (operatorMatrixPencilCauchy C₀ C z) :=
  operatorMatrixPencilCauchy_inverse_dyson C₀ C z
    (StarProbabilitySpace.selfAdjoint_mem_resolventSet_of_im_ne_zero (operatorMatrixPencil C₀ C)
      (operatorMatrixPencil_isSelfAdjoint C₀ C hC₀ hC) z hz)

end FreeProbability.Fock

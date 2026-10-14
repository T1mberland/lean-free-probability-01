import FreeProbability.OperatorValued.MatrixCreatorCalculus
import FreeProbability.OperatorValued.MatrixScalarEmbedding

/-! # Genuine completion of square for matrix semicircular pencils

The coefficients are arbitrary Hermitian matrices, not necessarily positive
or commuting. The square root parameter is initially an invertible Hermitian
matrix; the subsequent positive-matrix specialization supplies every test matrix.
-/

noncomputable section
open scoped Classical ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix
namespace FreeProbability.Fock

variable {I n : Type*} [Fintype I] [Fintype n] [DecidableEq n]
local instance : PartialOrder (WordSpace I →L[ℂ] WordSpace I) := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing (WordSpace I →L[ℂ] WordSpace I) :=
  CStarAlgebra.spectralOrderedRing _

/-- The actual creator completion-of-square operator. -/
def matrixSquareCertificate (S : Matrix n n ℂ) (C : I → Matrix n n ℂ) :
    Matrix n n (WordSpace I →L[ℂ] WordSpace I) :=
  scalarMatrixEmbedding S - matrixCreationCombination (fun i => S⁻¹ * C i)

/-- Exact ordered completion-of-square identity, using actual creation operators. -/
theorem matrixSquareCertificate_gram (S : Matrix n n ℂ) (hS : S.IsHermitian) (hSu : IsUnit S)
    (C : I → Matrix n n ℂ) (hC : ∀ i, (C i).IsHermitian) :
    (matrixSquareCertificate S C)ᴴ * matrixSquareCertificate S C =
      scalarMatrixEmbedding (S * S + matrixCovariance C (S⁻¹ * S⁻¹)) -
        matrixLinearCombination semicircular C := by
  let B : I → Matrix n n ℂ := fun i => S⁻¹ * C i
  have hl : scalarMatrixEmbedding S * matrixCreationCombination B = matrixCreationCombination C := by
    unfold matrixCreationCombination
    rw [scalarMatrix_mul_matrixLinearCombination]
    congr 1
    funext i
    dsimp [B]
    rw [← mul_assoc, Matrix.mul_nonsing_inv S ((Matrix.isUnit_iff_isUnit_det S).mp hSu), one_mul]
  have hr : (matrixCreationCombination B)ᴴ * scalarMatrixEmbedding S = matrixAnnihilationCombination C := by
    rw [matrixCreationCombination_conjTranspose]
    unfold matrixAnnihilationCombination
    rw [matrixLinearCombination_mul_scalarMatrix]
    congr 1
    funext i
    dsimp [B]
    rw [Matrix.conjTranspose_mul, (hC i).eq, hS.inv.eq, mul_assoc,
      Matrix.nonsing_inv_mul S ((Matrix.isUnit_iff_isUnit_det S).mp hSu), mul_one]
  have hg : ∑ i, (B i)ᴴ * B i = matrixCovariance C (S⁻¹ * S⁻¹) := by
    rw [matrixCovariance_apply]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [B]
    rw [Matrix.conjTranspose_mul, (hC i).eq, hS.inv.eq]
    simp only [mul_assoc]
  change (scalarMatrixEmbedding S - matrixCreationCombination B)ᴴ *
      (scalarMatrixEmbedding S - matrixCreationCombination B) = _
  rw [Matrix.conjTranspose_sub (scalarMatrixEmbedding (A := WordSpace I →L[ℂ] WordSpace I) S)
    (matrixCreationCombination B), scalarMatrixEmbedding_conjTranspose, hS.eq,
    sub_mul, mul_sub, mul_sub, hl, hr, matrixCreationCombination_gram, hg,
    ← map_mul, map_add, matrixLinearCombination_semicircular_eq]
  abel

/-- The actual affine pencil lies below the deterministic completion-of-square
matrix, in the genuine C-star matrix order. -/
theorem operatorMatrixPencil_le_square_bound (C₀ : Matrix n n ℂ)
    (S : Matrix n n ℂ) (hS : S.IsHermitian) (hSu : IsUnit S)
    (C : I → Matrix n n ℂ) (hC : ∀ i, (C i).IsHermitian) :
    operatorMatrixPencil C₀ C ≤ scalarCStarMatrixEmbedding
      (C₀ + S * S + matrixCovariance C (S⁻¹ * S⁻¹)) := by
  apply sub_nonneg.mp
  have hgram := matrixSquareCertificate_gram S hS hSu C hC
  have heq : scalarCStarMatrixEmbedding (C₀ + S * S + matrixCovariance C (S⁻¹ * S⁻¹)) -
      operatorMatrixPencil C₀ C =
      star (CStarMatrix.ofMatrix (matrixSquareCertificate S C)) *
        CStarMatrix.ofMatrix (matrixSquareCertificate S C) := by
    change CStarMatrix.ofMatrix
      (scalarMatrixEmbedding (C₀ + S * S + matrixCovariance C (S⁻¹ * S⁻¹)) -
        (scalarMatrixEmbedding C₀ + matrixLinearCombination semicircular C)) =
      CStarMatrix.ofMatrix ((matrixSquareCertificate S C)ᴴ * matrixSquareCertificate S C)
    apply congrArg CStarMatrix.ofMatrix
    rw [hgram]
    simp only [map_add]
    abel
  rw [heq]
  exact star_mul_self_nonneg _

/-- Every positive definite test matrix gives the genuine completion-of-square
upper bound `H ≤ embed(C₀ + Z + η(Z⁻¹))`. -/
theorem operatorMatrixPencil_le_positive_square_bound (C₀ : Matrix n n ℂ)
    (Z : Matrix n n ℂ) (hZ : Z.PosDef) (C : I → Matrix n n ℂ)
    (hC : ∀ i, (C i).IsHermitian) :
    operatorMatrixPencil C₀ C ≤ scalarCStarMatrixEmbedding (C₀ + Z + matrixCovariance C Z⁻¹) := by
  by_cases hn : Nonempty n
  · have := hn
    let S := CFC.sqrt Z
    have hSn : S.PosSemidef := (CFC.sqrt_nonneg Z).posSemidef
    have hSS : S * S = Z := CFC.sqrt_mul_sqrt_self Z hZ.posSemidef.nonneg
    have hSu : IsUnit S := isUnit_mul_self_iff.mp (hSS.symm ▸ hZ.isUnit)
    have hSi : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S ((Matrix.isUnit_iff_isUnit_det S).mp hSu)
    have hSii : S⁻¹ * S⁻¹ = Z⁻¹ := by
      symm
      apply Matrix.inv_eq_left_inv
      rw [← hSS, mul_assoc S⁻¹ S⁻¹ (S * S), ← mul_assoc S⁻¹ S S, hSi, one_mul, hSi]
    simpa only [hSS, hSii] using operatorMatrixPencil_le_square_bound C₀ S hSn.isHermitian hSu C hC
  · have : IsEmpty n := not_nonempty_iff.mp hn
    exact le_of_eq (CStarMatrix.ext (fun r _ => isEmptyElim r))

end FreeProbability.Fock

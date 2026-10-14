import FreeProbability.OperatorValued.MatrixSpectralMaximum

/-! # Actual matrix semicircular spectral-edge variational formula

The edge is the maximum of the genuine real operator spectrum, and `λmax` is
the proved largest eigenvalue of each finite Hermitian coefficient matrix.
Coefficients are arbitrary Hermitian matrices. No positivity or commutativity
assumptions are imposed on them, and no attainment at the edge is asserted.
-/

noncomputable section
open scoped Classical ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix
namespace FreeProbability

variable {I n : Type*} [Fintype I] [Fintype n] [DecidableEq n]

/-- Hermitian coefficients make the true covariance preserve Hermitian matrices. -/
theorem matrixCovariance_isHermitian (C : I → Matrix n n ℂ) (hC : ∀ i, (C i).IsHermitian)
    (D : Matrix n n ℂ) (hD : D.IsHermitian) : (matrixCovariance C D).IsHermitian := by
  change (∑ i, C i * D * C i)ᴴ = ∑ i, C i * D * C i
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, (hC i).eq, hD.eq]
  simp only [mul_assoc]

namespace Fock
variable [Nonempty n]
local instance : PartialOrder (WordSpace I →L[ℂ] WordSpace I) := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing (WordSpace I →L[ℂ] WordSpace I) :=
  CStarAlgebra.spectralOrderedRing _
local instance : Nontrivial (WordSpace I →L[ℂ] WordSpace I) := by
  refine ⟨⟨1, 0, ?_⟩⟩
  intro h
  have hv := congrArg (fun T : WordSpace I →L[ℂ] WordSpace I => ‖T vacuum‖) h
  simp at hv

/-- The top edge of the actual affine Fock matrix operator spectrum. -/
def operatorMatrixPencilTopEdge (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ) : ℝ :=
  realSpectralMaximum (operatorMatrixPencil C₀ C)

omit [Fintype I] [Nonempty n] in
private theorem scalarCStarMatrixEmbedding_real_scalar (x : ℝ) :
    scalarCStarMatrixEmbedding (A := WordSpace I →L[ℂ] WordSpace I)
      (algebraMap ℝ (Matrix n n ℂ) x) =
      algebraMap ℝ (CStarMatrix n n (WordSpace I →L[ℂ] WordSpace I)) x := by
  rw [IsScalarTower.algebraMap_apply ℝ ℂ (Matrix n n ℂ) x,
    IsScalarTower.algebraMap_apply ℝ ℂ (CStarMatrix n n (WordSpace I →L[ℂ] WordSpace I)) x]
  exact scalarCStarMatrixEmbedding.toAlgHom.commutes _

/-- Every positive definite test matrix bounds the genuine top spectral edge. -/
theorem operatorMatrixPencilTopEdge_le_variational_value (C₀ : Matrix n n ℂ)
    (C : I → Matrix n n ℂ) (hC₀ : C₀.IsHermitian) (hC : ∀ i, (C i).IsHermitian)
    (Z : Matrix n n ℂ) (hZ : Z.PosDef) :
    operatorMatrixPencilTopEdge C₀ C ≤ matrixMaxEigenvalue (C₀ + Z + matrixCovariance C Z⁻¹) := by
  let D := C₀ + Z + matrixCovariance C Z⁻¹
  have hD : D.IsHermitian := (hC₀.add hZ.isHermitian).add
    (matrixCovariance_isHermitian C hC _ hZ.isHermitian.inv)
  have hDbound := le_algebraMap_realSpectralMaximum D hD
  have hPbound := (operatorMatrixPencil_le_positive_square_bound C₀ Z hZ C hC).trans
    (scalarCStarMatrixEmbedding_mono (A := WordSpace I →L[ℂ] WordSpace I) hDbound)
  rw [scalarCStarMatrixEmbedding_real_scalar] at hPbound
  exact realSpectralMaximum_le_of_le_algebraMap (operatorMatrixPencil C₀ C)
    (operatorMatrixPencil_isSelfAdjoint C₀ C hC₀ hC) _ hPbound

/-- Every point strictly above the actual edge supplies a positive definite
Dyson test matrix whose variational matrix is exactly `x I`. -/
theorem operatorMatrixPencil_variational_witness (C₀ : Matrix n n ℂ)
    (C : I → Matrix n n ℂ) (hC₀ : C₀.IsHermitian) (hC : ∀ i, (C i).IsHermitian)
    (x : ℝ) (hx : operatorMatrixPencilTopEdge C₀ C < x) :
    ∃ Z : Matrix n n ℂ, Z.PosDef ∧ C₀ + Z + matrixCovariance C Z⁻¹ = (x : ℂ) • 1 := by
  have hright : ∀ t ∈ spectrum ℝ (operatorMatrixPencil C₀ C), t < x :=
    (realSpectralMaximum_lt_iff _ (operatorMatrixPencil_isSelfAdjoint C₀ C hC₀ hC) x).mp hx
  let M := operatorMatrixPencilCauchy C₀ C x
  have hM : M.PosDef := operatorMatrixPencilCauchy_posDef_right_exterior C₀ C hC₀ hC x hright
  have hMi : M⁻¹⁻¹ = M := by
    let := hM.isUnit.invertible
    exact Matrix.inv_inv_of_invertible M
  refine ⟨M⁻¹, hM.inv, ?_⟩
  rw [hMi]
  have hDy : M⁻¹ = (x : ℂ) • (1 : Matrix n n ℂ) - C₀ - matrixCovariance C M :=
    operatorMatrixPencilCauchy_inverse_dyson_right_exterior C₀ C x hright
  rw [hDy]
  abel

/-- The actual set of largest-eigenvalue variational test values. -/
def operatorMatrixPencilVariationalValues (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ) : Set ℝ :=
  {r | ∃ Z : Matrix n n ℂ, Z.PosDef ∧ matrixMaxEigenvalue (C₀ + Z + matrixCovariance C Z⁻¹) = r}

/-- The genuine top Fock matrix spectral edge is the infimum over ALL positive
definite test matrices of `λmax(C₀ + Z + Σᵢ Cᵢ Z⁻¹ Cᵢ)`. -/
theorem operatorMatrixPencilTopEdge_variational (C₀ : Matrix n n ℂ)
    (C : I → Matrix n n ℂ) (hC₀ : C₀.IsHermitian) (hC : ∀ i, (C i).IsHermitian) :
    operatorMatrixPencilTopEdge C₀ C = sInf (operatorMatrixPencilVariationalValues C₀ C) := by
  have hne : (operatorMatrixPencilVariationalValues C₀ C).Nonempty :=
    ⟨matrixMaxEigenvalue (C₀ + 1 + matrixCovariance C 1⁻¹), 1, PosDef.one, rfl⟩
  have hlower : ∀ r ∈ operatorMatrixPencilVariationalValues C₀ C,
      operatorMatrixPencilTopEdge C₀ C ≤ r := by
    rintro r ⟨Z, hZ, rfl⟩
    exact operatorMatrixPencilTopEdge_le_variational_value C₀ C hC₀ hC Z hZ
  have hbd : BddBelow (operatorMatrixPencilVariationalValues C₀ C) :=
    ⟨operatorMatrixPencilTopEdge C₀ C, hlower⟩
  apply le_antisymm (le_csInf hne hlower)
  by_contra h
  have hstrict : operatorMatrixPencilTopEdge C₀ C < sInf (operatorMatrixPencilVariationalValues C₀ C) :=
    lt_of_not_ge h
  let x := (operatorMatrixPencilTopEdge C₀ C + sInf (operatorMatrixPencilVariationalValues C₀ C)) / 2
  have hx : operatorMatrixPencilTopEdge C₀ C < x := by dsimp [x]; linarith
  obtain ⟨Z, hZ, hvalue⟩ := operatorMatrixPencil_variational_witness C₀ C hC₀ hC x hx
  have hxmem : x ∈ operatorMatrixPencilVariationalValues C₀ C := by
    refine ⟨Z, hZ, ?_⟩
    rw [hvalue, matrixMaxEigenvalue_scalar]
  have hi := csInf_le hbd hxmem
  dsimp [x] at hi
  linarith

end Fock
end FreeProbability

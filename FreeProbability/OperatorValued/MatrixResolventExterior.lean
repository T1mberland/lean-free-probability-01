import FreeProbability.OperatorValued.MatrixPhysicalBranchUniqueness

/-! # Genuine matrix resolvent and Dyson identities outside the operator norm

The radius is the actual C-star norm of the affine matrix pencil. The empty
matrix dimension is handled explicitly rather than imposing a nonempty premise.
-/

noncomputable section
open scoped Classical
namespace FreeProbability.Fock

variable {I n : Type*} [Fintype I] [Fintype n] [DecidableEq n]
local instance : PartialOrder (WordSpace I →L[ℂ] WordSpace I) := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing (WordSpace I →L[ℂ] WordSpace I) :=
  CStarAlgebra.spectralOrderedRing _

/-- All arguments outside the actual operator-norm disk belong to the true
matrix-pencil resolvent domain, even for non-Hermitian coefficients. -/
theorem operatorMatrixPencil_mem_resolventSet_of_norm_lt (C₀ : Matrix n n ℂ)
    (C : I → Matrix n n ℂ) (z : ℂ) (hz : ‖operatorMatrixPencil C₀ C‖ < ‖z‖) :
    z ∈ resolventSet ℂ (operatorMatrixPencil C₀ C) := by
  by_cases hn : Nonempty n
  · have := hn
    have : Nontrivial (WordSpace I →L[ℂ] WordSpace I) := by
      refine ⟨⟨1, 0, ?_⟩⟩
      intro h
      have hv := congrArg (fun T : WordSpace I →L[ℂ] WordSpace I => ‖T vacuum‖) h
      simp at hv
    exact spectrum.mem_resolventSet_of_norm_lt hz
  · have : IsEmpty n := not_nonempty_iff.mp hn
    have : Subsingleton (CStarMatrix n n (WordSpace I →L[ℂ] WordSpace I)) :=
      ⟨fun X Y => CStarMatrix.ext (fun r _ => isEmptyElim r)⟩
    have he : algebraMap ℂ (CStarMatrix n n (WordSpace I →L[ℂ] WordSpace I)) z -
        operatorMatrixPencil C₀ C = 1 := Subsingleton.elim _ _
    change IsUnit (algebraMap ℂ _ z - operatorMatrixPencil C₀ C)
    rw [he]
    exact isUnit_one

/-- Actual inverse Dyson on the full exterior of the genuine operator-norm disk. -/
theorem operatorMatrixPencilCauchy_inverse_dyson_exterior (C₀ : Matrix n n ℂ)
    (C : I → Matrix n n ℂ) (z : ℂ) (hz : ‖operatorMatrixPencil C₀ C‖ < ‖z‖) :
    (operatorMatrixPencilCauchy C₀ C z)⁻¹ = z • (1 : Matrix n n ℂ) - C₀ -
      matrixCovariance C (operatorMatrixPencilCauchy C₀ C z) :=
  operatorMatrixPencilCauchy_inverse_dyson C₀ C z
    (operatorMatrixPencil_mem_resolventSet_of_norm_lt C₀ C z hz)

/-- In particular the same actual Dyson identity is available at real arguments
on either side of the genuine matrix-pencil norm bound. -/
theorem operatorMatrixPencilCauchy_inverse_dyson_real_exterior (C₀ : Matrix n n ℂ)
    (C : I → Matrix n n ℂ) (x : ℝ) (hx : ‖operatorMatrixPencil C₀ C‖ < |x|) :
    (operatorMatrixPencilCauchy C₀ C x)⁻¹ = (x : ℂ) • (1 : Matrix n n ℂ) - C₀ -
      matrixCovariance C (operatorMatrixPencilCauchy C₀ C x) :=
  operatorMatrixPencilCauchy_inverse_dyson_exterior C₀ C x (by simpa using hx)

end FreeProbability.Fock

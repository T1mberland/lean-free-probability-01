import FreeProbability.OperatorValued.MatrixPositiveExpectation
import Mathlib.Analysis.Matrix.Order

/-! # Genuine star-algebra embedding of deterministic scalar matrices -/

noncomputable section
open scoped Classical ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix
namespace FreeProbability

variable {A n : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [Fintype n] [DecidableEq n]

/-- Embed deterministic complex matrices into the actual amplified C-star algebra. -/
def scalarCStarMatrixEmbedding : Matrix n n ℂ →⋆ₐ[ℂ] CStarMatrix n n A where
  toAlgHom := CStarMatrix.ofMatrixStarAlgEquiv.toAlgEquiv.toAlgHom.comp scalarMatrixEmbedding
  map_star' C := by
    apply CStarMatrix.ext
    intro r c
    change algebraMap ℂ A (star (C c r)) = star (algebraMap ℂ A (C c r))
    exact algebraMap_star_comm _

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem scalarCStarMatrixEmbedding_apply (C : Matrix n n ℂ) :
    scalarCStarMatrixEmbedding (A := A) C = CStarMatrix.ofMatrix (scalarMatrixEmbedding C) := rfl

omit [PartialOrder A] [StarOrderedRing A] in
/-- The deterministic embedding respects the literal matrix conjugate transpose. -/
theorem scalarMatrixEmbedding_conjTranspose (C : Matrix n n ℂ) :
    (scalarMatrixEmbedding (A := A) C)ᴴ = scalarMatrixEmbedding Cᴴ := by
  apply Matrix.ext
  intro r c
  change star (algebraMap ℂ A (C c r)) = algebraMap ℂ A (star (C c r))
  exact (algebraMap_star_comm _).symm

/-- The actual deterministic matrix embedding preserves the full positive cone. -/
theorem scalarCStarMatrixEmbedding_nonneg (C : Matrix n n ℂ) (hC : C.PosSemidef) :
    0 ≤ scalarCStarMatrixEmbedding (A := A) C :=
  map_nonneg scalarCStarMatrixEmbedding hC.nonneg

/-- Scalar matrix positivity gives an actual operator-matrix comparison. -/
theorem scalarCStarMatrixEmbedding_mono {C D : Matrix n n ℂ} (h : C ≤ D) :
    scalarCStarMatrixEmbedding (A := A) C ≤ scalarCStarMatrixEmbedding D :=
  OrderHomClass.monotone scalarCStarMatrixEmbedding h

end FreeProbability

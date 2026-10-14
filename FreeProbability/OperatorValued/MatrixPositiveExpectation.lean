import FreeProbability.OperatorValued.MatrixStatePositivity
import Mathlib.Analysis.CStarAlgebra.CStarMatrix

/-! # Actual scalar-state matrix expectation preserves the full positive cone

Positivity is proved for every positive C-star matrix, without a supplied
complete-positivity premise or a restriction to explicitly supplied Gram inputs.
-/

noncomputable section
open scoped Classical ComplexOrder
open Matrix
namespace FreeProbability

variable {A n : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- Entrywise averaging by an actual positive scalar state preserves every
positive C-star matrix at every finite matrix dimension. -/
theorem matrixExpectation_posSemidef_of_cstarMatrix_nonneg (φ : StarProbabilitySpace A)
    (X : CStarMatrix n n A) (hX : 0 ≤ X) :
    (matrixExpectation φ.toProbabilitySpace (CStarMatrix.ofMatrix.symm X)).PosSemidef := by
  have hx := StarOrderedRing.nonneg_iff.mp hX
  refine AddSubmonoid.closure_induction
    (motive := fun M _ => (matrixExpectation φ.toProbabilitySpace
      (CStarMatrix.ofMatrix.symm M)).PosSemidef) ?_ ?_ ?_ hx
  · intro M hM
    obtain ⟨Y, rfl⟩ := hM
    change (matrixExpectation φ.toProbabilitySpace
      ((CStarMatrix.ofMatrix.symm Y)ᴴ * CStarMatrix.ofMatrix.symm Y)).PosSemidef
    exact matrixExpectation_gram_posSemidef φ _
  · change (matrixExpectation φ.toProbabilitySpace (0 : Matrix n n A)).PosSemidef
    rw [map_zero]
    exact PosSemidef.zero
  · intro M N _ _ hM hN
    change (matrixExpectation φ.toProbabilitySpace
      (CStarMatrix.ofMatrix.symm M + CStarMatrix.ofMatrix.symm N)).PosSemidef
    rw [map_add]
    exact hM.add hN

end FreeProbability

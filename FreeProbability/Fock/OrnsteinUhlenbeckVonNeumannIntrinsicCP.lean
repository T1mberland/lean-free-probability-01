import FreeProbability.Fock.TensorFamilyVonNeumann
import FreeProbability.Fock.OrnsteinUhlenbeckVonNeumannRangeCP

/-! Intrinsic unital CP rotation-compression maps on literal prescribed-field double commutants.
The family is arbitrary: no orthonormality or spanning assumption is used. -/
noncomputable section
open scoped Classical CStarAlgebra
namespace FreeProbability.Fock
attribute [local irreducible] fullFockTensorDecomposition isometryPrefixTargetUnitary
  isometrySuffixEmbedding wordSuffixEmbedding doubledRotation secondQuantization isometryPrefixEmbedding
  doubledFockRotation doubledFirst doubledSecond fullFockBasis tensorCreation tensorAnnihilation tensorFamilyField
variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Canonical positive order on the actual closed double-commutant algebra. -/
instance tensorFamilyDoubleAlgebraOrder (e : I → H) : PartialOrder (tensorFamilyDoubleAlgebra e) :=
  CStarAlgebra.spectralOrder _

instance tensorFamilyDoubleAlgebraStarOrderedRing (e : I → H) :
    StarOrderedRing (tensorFamilyDoubleAlgebra e) := CStarAlgebra.spectralOrderedRing _

/-- Actual subtype inclusion reflects every canonical finite matrix cone. -/
theorem tensorFamilyDoubleMatrix_nonneg_of_coe {N : Type*} [Fintype N] (e : I → H)
    (M : CStarMatrix N N (tensorFamilyDoubleAlgebra e))
    (hM : 0 ≤ M.map (tensorFamilyDoubleAlgebra e).val) : 0 ≤ M := by
  let F : CStarMatrix N N (tensorFamilyDoubleAlgebra e) →⋆ₙₐ[ℂ]
      CStarMatrix N N (TensorFullFock H →L[ℂ] TensorFullFock H) :=
    CStarMatrix.mapₙₐ (tensorFamilyDoubleAlgebra e).subtype.toNonUnitalStarAlgHom
  have hF : Function.Injective F := by
    intro A B h
    apply CStarMatrix.ext
    intro i j
    apply Subtype.ext
    exact congrArg (fun X : CStarMatrix N N (TensorFullFock H →L[ℂ] TensorFullFock H) => X i j) h
  have hh : F 0 ≤ F M := by
    rw [map_zero]
    exact hM
  exact (NonUnitalStarAlgHom.map_le_map_iff F hF).mp hh

/-- The ambient rotation-dilation restricted to its proved literal double-commutant range. -/
def ouVonNeumannLinear (e : I → H) (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1) :
    tensorFamilyDoubleAlgebra e →ₗ[ℂ] tensorFamilyDoubleAlgebra e where
  toFun T := ⟨ouDoubleCommutantRawCP (H := H) r s hrs T, by
    change ouDoubleCommutantRawCP (H := H) r s hrs T ∈ (tensorFamilyDoubleAlgebra e : Set _)
    rw [tensorFamilyDoubleAlgebra_coe]
    apply ouDoubleCommutantRawCP_mem_familyDoubleCentralizer r s hrs e
    rw [← tensorFamilyDoubleAlgebra_coe]
    exact T.property⟩
  map_add' T S := by
    apply Subtype.ext
    exact map_add (ouDoubleCommutantRawCP (H := H) r s hrs)
      (T : TensorFullFock H →L[ℂ] TensorFullFock H) (S : TensorFullFock H →L[ℂ] TensorFullFock H)
  map_smul' c T := by
    apply Subtype.ext
    exact map_smul (ouDoubleCommutantRawCP (H := H) r s hrs).toLinearMap c
      (T : TensorFullFock H →L[ℂ] TensorFullFock H)

/-- Genuine complete positivity of the actual double-commutant self-map at every finite matrix level. -/
def ouVonNeumannCP (e : I → H) (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1) :
    tensorFamilyDoubleAlgebra e →CP tensorFamilyDoubleAlgebra e where
  toLinearMap := ouVonNeumannLinear e r s hrs
  map_cstarMatrix_nonneg' _n M hM := by
    apply tensorFamilyDoubleMatrix_nonneg_of_coe e
    have hi : 0 ≤ M.map (tensorFamilyDoubleAlgebra e).val :=
      map_nonneg (CStarMatrix.mapₙₐ (tensorFamilyDoubleAlgebra e).subtype.toNonUnitalStarAlgHom) hM
    exact (ouDoubleCommutantRawCP (H := H) r s hrs).map_cstarMatrix_nonneg
      (M.map (tensorFamilyDoubleAlgebra e).val) hi

@[simp] theorem ouVonNeumannCP_coe (e : I → H) (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1)
    (T : tensorFamilyDoubleAlgebra e) :
    (ouVonNeumannCP e r s hrs T : TensorFullFock H →L[ℂ] TensorFullFock H) =
      ouDoubleCommutantRawCP (H := H) r s hrs T := rfl

@[simp] theorem ouVonNeumannCP_one (e : I → H) (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1) :
    ouVonNeumannCP e r s hrs 1 = 1 := by
  apply Subtype.ext
  exact ouDoubleCommutantRawCP_one r s hrs

 theorem norm_ouVonNeumannCP_le (e : I → H) (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1)
    (T : tensorFamilyDoubleAlgebra e) : ‖ouVonNeumannCP e r s hrs T‖ ≤ ‖T‖ :=
  norm_ouDoubleCommutantRawCP_le (H := H) r s hrs
    (T : TensorFullFock H →L[ℂ] TensorFullFock H)

/-- The genuine positive normalized vacuum state is preserved on the whole double commutant. -/
theorem ouVonNeumannCP_expectation (e : I → H) (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1)
    (T : tensorFamilyDoubleAlgebra e) :
    (tensorFamilyVonNeumannVacuumState e).expectation (ouVonNeumannCP e r s hrs T) =
      (tensorFamilyVonNeumannVacuumState e).expectation T :=
  ouDoubleCommutantRawCP_vacuum_expectation (H := H) r s hrs
    (T : TensorFullFock H →L[ℂ] TensorFullFock H)

end FreeProbability.Fock

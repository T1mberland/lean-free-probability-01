import FreeProbability.Fock.OrnsteinUhlenbeckVonNeumannRange

/-! # Actual all-matrix CP, unit, norm and vacuum properties of the OU dilation map

The literal double-commutant range is separately proved. Normality and
semigroup laws are not consequences asserted here.
-/
noncomputable section
open scoped Classical CStarAlgebra
namespace FreeProbability.Fock
attribute [local irreducible] fullFockTensorDecomposition isometryPrefixTargetUnitary
  isometrySuffixEmbedding wordSuffixEmbedding doubledRotation secondQuantization isometryPrefixEmbedding
  doubledFockRotation doubledFirst doubledSecond fullFockBasis tensorCreation tensorAnnihilation tensorFamilyField
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Actual all-operator OU rotation-dilation, completely positive at EVERY canonical finite matrix level. -/
def ouDoubleCommutantRawCP (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1) :
    (TensorFullFock H →L[ℂ] TensorFullFock H) →CP (TensorFullFock H →L[ℂ] TensorFullFock H) where
  toLinearMap := ouDoubleCommutantRaw r s hrs
  map_cstarMatrix_nonneg' _n M hM := by
    let Φ := isometryPrefixEmbedding (doubledFirst H)
    have hΦ : 0 ≤ M.map Φ := map_nonneg (CStarMatrix.mapₙₐ Φ.toNonUnitalStarAlgHom) hM
    have hR := (rotatedFockCompression H r s hrs).map_cstarMatrix_nonneg (M.map Φ) hΦ
    have he : M.map (ouDoubleCommutantRaw r s hrs) =
        (M.map Φ).map (rotatedFockCompression H r s hrs) := by
      apply CStarMatrix.ext
      intro i j
      rfl
    rw [he]
    exact hR

@[simp] theorem ouDoubleCommutantRawCP_apply (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1)
    (T : TensorFullFock H →L[ℂ] TensorFullFock H) :
    ouDoubleCommutantRawCP r s hrs T =
      rotatedFockCompression H r s hrs (isometryPrefixEmbedding (doubledFirst H) T) := rfl

@[simp] theorem ouDoubleCommutantRawCP_one (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1) :
    ouDoubleCommutantRawCP (H := H) r s hrs 1 = 1 := by
  rw [ouDoubleCommutantRawCP_apply, map_one, rotatedFockCompression_one]

/-- True operator-norm contraction on ALL source bounded operators. -/
theorem norm_ouDoubleCommutantRawCP_le (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1)
    (T : TensorFullFock H →L[ℂ] TensorFullFock H) :
    ‖ouDoubleCommutantRawCP r s hrs T‖ ≤ ‖T‖ := by
  rw [ouDoubleCommutantRawCP_apply]
  have hi : ‖isometryPrefixEmbedding (doubledFirst H) T‖ = ‖T‖ :=
    NonUnitalStarAlgHom.norm_map _ (isometryPrefixEmbedding_injective _) T
  exact (norm_rotatedFockCompression_le H r s hrs _).trans hi.le

/-- The actual normalized ambient vacuum state is preserved on ALL source bounded operators. -/
theorem ouDoubleCommutantRawCP_vacuum_expectation (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1)
    (T : TensorFullFock H →L[ℂ] TensorFullFock H) :
    (tensorVacuumState H).expectation (ouDoubleCommutantRawCP r s hrs T) =
      (tensorVacuumState H).expectation T := by
  rw [ouDoubleCommutantRawCP_apply, tensorVacuumState_expectation, tensorVacuumState_expectation]
  have hr := rotatedFockCompression_vacuum_expectation H r s hrs
    (isometryPrefixEmbedding (doubledFirst H) T)
  have hi := isometryPrefixEmbedding_vacuum_expectation (doubledFirst H) T
  rw [tensorVacuumState_expectation, tensorVacuumState_expectation] at hi
  exact hr.trans hi

/-- All-matrix CP map has the already verified literal prescribed-family double-commutant range. -/
theorem ouDoubleCommutantRawCP_mem_familyDoubleCentralizer {I : Type*}
    (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1) (e : I → H)
    {T : TensorFullFock H →L[ℂ] TensorFullFock H}
    (hT : T ∈ Set.centralizer (Set.centralizer (Set.range (tensorFamilyField e)))) :
    ouDoubleCommutantRawCP r s hrs T ∈ Set.centralizer (Set.centralizer (Set.range (tensorFamilyField e))) :=
  ouDoubleCommutantRaw_mem_familyDoubleCentralizer r s hrs e hT

end FreeProbability.Fock

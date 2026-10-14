import FreeProbability.Fock.OrnsteinUhlenbeckVonNeumannIntrinsicTime
import FreeProbability.Fock.OrnsteinUhlenbeckVonNeumannRangeWOT

/-! The intrinsic OU map is continuous on each concrete double-commutant WOT norm ball.
This does not assert continuity on unbounded WOT nets or order-supremum normality. -/
noncomputable section
open scoped Classical CStarAlgebra NNReal
namespace FreeProbability.Fock
attribute [local irreducible] fullFockTensorDecomposition isometryPrefixTargetUnitary
  isometrySuffixEmbedding wordSuffixEmbedding doubledRotation secondQuantization isometryPrefixEmbedding
  doubledFockRotation doubledFirst doubledSecond fullFockBasis tensorCreation tensorAnnihilation tensorFamilyField
variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The literal prescribed-field double commutant intersected with a bounded operator norm ball,
carrying the subspace topology from genuine ambient WOT. -/
abbrev ouVonNeumannWOTNormBall (e : I → H) (C : ℝ≥0) :=
  {T : WOTNormBall (TensorFullFock H) C // T.val.toCLM ∈ tensorFamilyDoubleAlgebra e}

private def ouIntrinsicAmbientBall (t : ℝ) (ht : 0 ≤ t) (C : ℝ≥0) :
    WOTNormBall (TensorFullFock H) C → WOTNormBall (TensorFullFock H) C := fun T =>
  ⟨ContinuousLinearMapWOT.ofCLM (ouDoubleCommutantTimeCP (H := H) t ht T.val.toCLM),
    (norm_ouDoubleCommutantTimeCP_le t ht T.val.toCLM).trans T.property⟩

private theorem ouIntrinsicAmbientBall_continuous (t : ℝ) (ht : 0 ≤ t) (C : ℝ≥0) :
    Continuous (ouIntrinsicAmbientBall (H := H) t ht C) :=
  (ouDoubleCommutantTimeCP_boundedWOT_continuous t ht C).subtype_mk _

/-- The actual intrinsic CP map, represented as a self-map of its concrete WOT norm ball. -/
def ouVonNeumannTimeWOTNormBall (e : I → H) (t : ℝ) (ht : 0 ≤ t) (C : ℝ≥0) :
    ouVonNeumannWOTNormBall e C → ouVonNeumannWOTNormBall e C := fun T =>
  ⟨ouIntrinsicAmbientBall t ht C T.val, by
    change ouDoubleCommutantTimeCP (H := H) t ht T.val.val.toCLM ∈
      (tensorFamilyDoubleAlgebra e : Set (TensorFullFock H →L[ℂ] TensorFullFock H))
    rw [tensorFamilyDoubleAlgebra_coe]
    apply ouDoubleCommutantTimeCP_mem_familyDoubleCentralizer t ht e
    rw [← tensorFamilyDoubleAlgebra_coe]
    exact T.property⟩

/-- Exact agreement with the intrinsic CP map on the same genuine operator. -/
theorem ouVonNeumannTimeWOTNormBall_toCLM (e : I → H) (t : ℝ) (ht : 0 ≤ t) (C : ℝ≥0)
    (T : ouVonNeumannWOTNormBall e C) :
    (ouVonNeumannTimeWOTNormBall e t ht C T).val.val.toCLM =
      (ouVonNeumannTimeCP e t ht ⟨T.val.val.toCLM, T.property⟩ :
        TensorFullFock H →L[ℂ] TensorFullFock H) := rfl

/-- Genuine WOT continuity on every intrinsic uniform norm ball. -/
theorem ouVonNeumannTimeWOTNormBall_continuous (e : I → H) (t : ℝ) (ht : 0 ≤ t) (C : ℝ≥0) :
    Continuous (ouVonNeumannTimeWOTNormBall e t ht C) :=
  ((ouIntrinsicAmbientBall_continuous t ht C).comp continuous_subtype_val).subtype_mk _

end FreeProbability.Fock

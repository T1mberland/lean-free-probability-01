import FreeProbability.Fock.OrnsteinUhlenbeckVonNeumannIntrinsicTime
import FreeProbability.Fock.OrnsteinUhlenbeckL2WickVacuum

/-! The actual Hilbert-space sandwich of the OU rotation, on all completed Fock vectors. -/
noncomputable section
open scoped Classical InnerProductSpace
namespace FreeProbability.Fock
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Actual second-quantized rotation followed by included-space compression. -/
def ouVacuumSandwich (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1) :
    TensorFullFock H →L[ℂ] TensorFullFock H :=
  (doubledFockInclusion H).toContinuousLinearMap.adjoint.comp
    ((doubledFockRotation H r s hrs).toLinearIsometry.toContinuousLinearMap.comp
      (doubledFockInclusion H).toContinuousLinearMap)

 theorem ouVacuumSandwich_creation (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1)
    (h : H) (f : TensorFullFock H) :
    ouVacuumSandwich r s hrs (tensorCreation H h f) =
      (r : ℂ) • tensorCreation H h (ouVacuumSandwich r s hrs f) := by
  have hi := DFunLike.congr_fun (secondQuantizationIsometry_creation_comp (doubledFirst H) h) f
  change doubledFockInclusion H (tensorCreation H h f) =
    tensorCreation (DoubledHilbert H) (doubledFirst H h) (doubledFockInclusion H f) at hi
  change (doubledFockInclusion H).toContinuousLinearMap.adjoint
    (doubledFockRotation H r s hrs (doubledFockInclusion H (tensorCreation H h f))) = _
  rw [hi]
  have hr := secondQuantization_creation (doubledRotation r s hrs)
    (doubledFirst H h) (doubledFockInclusion H f)
  change doubledFockRotation H r s hrs
    (tensorCreation (DoubledHilbert H) (doubledFirst H h) (doubledFockInclusion H f)) =
    tensorCreation (DoubledHilbert H) (doubledRotation r s hrs (doubledFirst H h))
      (doubledFockRotation H r s hrs (doubledFockInclusion H f)) at hr
  rw [hr, rotated_creator_left_projection]
  rfl

@[simp] theorem ouVacuumSandwich_vacuum (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1) :
    ouVacuumSandwich (H := H) r s hrs (tensorVacuum H) = tensorVacuum H := by
  change (secondQuantizationIsometry (doubledFirst H)).toContinuousLinearMap.adjoint
    (secondQuantization (doubledRotation r s hrs)
      (secondQuantizationIsometry (doubledFirst H) (tensorVacuum H))) = _
  rw [secondQuantizationIsometry_vacuum, secondQuantization_vacuum]
  rw [← secondQuantizationIsometry_vacuum (doubledFirst H)]
  exact DFunLike.congr_fun (secondQuantizationIsometry_adjoint_comp (doubledFirst H)) (tensorVacuum H)

 theorem ouVacuumSandwich_creatorWord (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1) (w : List H) :
    ouVacuumSandwich r s hrs (tensorCreatorWord w (tensorVacuum H)) =
      (r : ℂ) ^ w.length • tensorCreatorWord w (tensorVacuum H) := by
  induction w with
  | nil => simp
  | cons h w ih =>
    change ouVacuumSandwich r s hrs (tensorCreation H h (tensorCreatorWord w (tensorVacuum H))) = _
    rw [ouVacuumSandwich_creation, ih, map_smul, smul_smul]
    simp only [List.length_cons, pow_succ', tensorCreatorWord_cons, mul_apply_eq_comp]

end FreeProbability.Fock

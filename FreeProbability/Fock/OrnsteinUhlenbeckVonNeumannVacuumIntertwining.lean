import FreeProbability.Fock.OrnsteinUhlenbeckVonNeumannVacuumDamping

/-! Actual all-bounded-operator vacuum-vector intertwining, without polynomial-density assumptions. -/
noncomputable section
open scoped Classical InnerProductSpace
namespace FreeProbability.Fock
variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual ambient CP rotation-dilation acts on every vacuum vector by its Hilbert sandwich. -/
theorem ouDoubleCommutantRawCP_vacuum_vector (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1)
    (T : TensorFullFock H →L[ℂ] TensorFullFock H) :
    ouDoubleCommutantRawCP r s hrs T (tensorVacuum H) =
      ouVacuumSandwich r s hrs (T (tensorVacuum H)) := by
  have hv : (doubledFockRotation H r s hrs).symm (tensorVacuum (DoubledHilbert H)) =
      tensorVacuum (DoubledHilbert H) := by
    apply (doubledFockRotation H r s hrs).injective
    rw [LinearIsometryEquiv.apply_symm_apply, doubledFockRotation_vacuum]
  have hi := isometryPrefixEmbedding_inclusion (doubledFirst H) T (tensorVacuum H)
  change (doubledFockInclusion H).toContinuousLinearMap.adjoint
    (doubledFockRotation H r s hrs
      (isometryPrefixEmbedding (doubledFirst H) T
        ((doubledFockRotation H r s hrs).symm (doubledFockInclusion H (tensorVacuum H))))) = _
  rw [doubledFockInclusion_vacuum, hv, ← doubledFockInclusion_vacuum H]
  change (doubledFockInclusion H).toContinuousLinearMap.adjoint
    (doubledFockRotation H r s hrs
      (isometryPrefixEmbedding (doubledFirst H) T
        (secondQuantizationIsometry (doubledFirst H) (tensorVacuum H)))) = _
  rw [hi]
  rfl

/-- Every bounded tensor-Fock operator has the exact degree-damped vacuum image under actual OU. -/
theorem ouDoubleCommutantTimeCP_vacuum_vector (t : ℝ) (ht : 0 ≤ t)
    (T : TensorFullFock H →L[ℂ] TensorFullFock H) :
    ouDoubleCommutantTimeCP t ht T (tensorVacuum H) = degreeDamping H t ht (T (tensorVacuum H)) := by
  change ouDoubleCommutantRawCP (ouCosine t) (ouSine t) (ouRotation_parameters t ht) T
    (tensorVacuum H) = _
  rw [ouDoubleCommutantRawCP_vacuum_vector, ouVacuumSandwich_eq_degreeDamping]

/-- Exact intertwining on the whole literal prescribed-family double commutant, for any family. -/
theorem ouVonNeumannTimeCP_vacuum_vector (e : I → H) (t : ℝ) (ht : 0 ≤ t)
    (T : tensorFamilyDoubleAlgebra e) :
    (ouVonNeumannTimeCP e t ht T : TensorFullFock H →L[ℂ] TensorFullFock H) (tensorVacuum H) =
      degreeDamping H t ht ((T : TensorFullFock H →L[ℂ] TensorFullFock H) (tensorVacuum H)) :=
  ouDoubleCommutantTimeCP_vacuum_vector t ht (T : TensorFullFock H →L[ℂ] TensorFullFock H)

end FreeProbability.Fock

import FreeProbability.Fock.OrnsteinUhlenbeckVonNeumannVacuumSemigroup
import FreeProbability.Fock.OrnsteinUhlenbeckContinuityHilbert

/-! Whole-double-commutant vacuum L2 contraction and actual strong continuity of vacuum images.
For an ON family vacuum evaluation is injective. No identification of a nonspanning
family's cyclic Hilbert space with all ambient Fock space is assumed. -/
noncomputable section
open scoped Classical InnerProductSpace NNReal
namespace FreeProbability.Fock
variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Actual bounded vacuum evaluation on the complete prescribed-family double commutant. -/
def ouVonNeumannVacuumVector (e : I → H) : tensorFamilyDoubleAlgebra e →L[ℂ] TensorFullFock H :=
  ({ toFun := fun T => (T : TensorFullFock H →L[ℂ] TensorFullFock H) (tensorVacuum H)
     map_add' := by intro T S; rfl
     map_smul' := by intro c T; rfl } : tensorFamilyDoubleAlgebra e →ₗ[ℂ] TensorFullFock H).mkContinuous 1 (by
    intro T
    have ht := (T : TensorFullFock H →L[ℂ] TensorFullFock H).le_opNorm (tensorVacuum H)
    rw [norm_tensorVacuum, mul_one] at ht
    exact ht.trans (one_mul _).symm.le)

 theorem ouVonNeumannVacuumVector_injective (e : I → H) (he : Orthonormal ℂ e) :
    Function.Injective (ouVonNeumannVacuumVector e) := by
  intro T S h
  exact ouVonNeumann_vacuum_ext e he T S h

 theorem ouVonNeumannTimeCP_vacuum_norm_le (e : I → H) (t : ℝ) (ht : 0 ≤ t)
    (T : tensorFamilyDoubleAlgebra e) :
    ‖ouVonNeumannVacuumVector e (ouVonNeumannTimeCP e t ht T)‖ ≤ ‖ouVonNeumannVacuumVector e T‖ := by
  change ‖(ouVonNeumannTimeCP e t ht T : TensorFullFock H →L[ℂ] TensorFullFock H)
    (tensorVacuum H)‖ ≤ _
  rw [ouVonNeumannTimeCP_vacuum_vector]
  exact norm_degreeDamping_le H t ht _

/-- The actual state's quadratic form is the squared norm of the actual vacuum vector. -/
theorem ouVonNeumannVacuumState_star_self_norm (e : I → H) (T : tensorFamilyDoubleAlgebra e) :
    (tensorFamilyVonNeumannVacuumState e).expectation (star T * T) =
      (‖ouVonNeumannVacuumVector e T‖ : ℂ) ^ 2 := by
  change (tensorVacuumState H).expectation
    (star (T : TensorFullFock H →L[ℂ] TensorFullFock H) * T) = _
  rw [tensorVacuumState_expectation, mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  rfl

/-- Genuine state L2 contraction on EVERY element of the whole double commutant. -/
theorem ouVonNeumannTimeCP_state_L2_le (e : I → H) (t : ℝ) (ht : 0 ≤ t)
    (T : tensorFamilyDoubleAlgebra e) :
    ((tensorFamilyVonNeumannVacuumState e).expectation
      (star (ouVonNeumannTimeCP e t ht T) * ouVonNeumannTimeCP e t ht T)).re ≤
      ((tensorFamilyVonNeumannVacuumState e).expectation (star T * T)).re := by
  rw [ouVonNeumannVacuumState_star_self_norm, ouVonNeumannVacuumState_star_self_norm]
  simp only [← Complex.ofReal_pow, Complex.ofReal_re]
  exact pow_le_pow_left₀ (norm_nonneg _) (ouVonNeumannTimeCP_vacuum_norm_le e t ht T) 2

/-- Strong time continuity, including time zero, of the actual whole-algebra vacuum images. -/
theorem ouVonNeumannTimeCP_vacuum_strong_continuous (e : I → H) (T : tensorFamilyDoubleAlgebra e) :
    Continuous (fun t : ℝ≥0 => ouVonNeumannVacuumVector e (ouVonNeumannTimeCP e t t.coe_nonneg T)) := by
  change Continuous (fun t : ℝ≥0 =>
    (ouVonNeumannTimeCP e t t.coe_nonneg T : TensorFullFock H →L[ℂ] TensorFullFock H) (tensorVacuum H))
  simp only [ouVonNeumannTimeCP_vacuum_vector]
  exact degreeDamping_strong_continuous H _

end FreeProbability.Fock

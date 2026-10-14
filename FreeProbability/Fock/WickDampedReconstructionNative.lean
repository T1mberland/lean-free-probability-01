import FreeProbability.Fock.WickDampedReconstructionVacuum
import FreeProbability.Fock.FamilyCyclicBasisNativeEquiv

/-! # Genuine positive-time OU regularization into the original native C-star algebra -/
noncomputable section
open scoped Classical InnerProductSpace
namespace FreeProbability.Fock
variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual whole-algebra OU image equals norm-convergent Wick reconstruction under the faithful word representation. -/
theorem familyWordRepresentation_ou_eq_dampedWick (e : I → H) (he : Orthonormal ℂ e)
    (t : ℝ) (ht : 0 < t) (T : tensorFamilyDoubleAlgebra e) :
    familyWordRepresentation e he (ouVonNeumannTimeCP e t ht.le T) =
      dampedWickReconstruction (Real.exp (-t) : ℂ) (familyVonNeumannWordCoefficients e he T) := by
  apply sub_eq_zero.mp
  apply eq_zero_of_commute_right_of_vacuum_eq_zero
  · intro i
    exact Commute.sub_left (familyWordRepresentation_commute_right e he _ i)
      (commute_right_of_mem_closedSemicircularAlgebra
        (dampedWickReconstruction_mem_closedAlgebra _ (norm_ouWickParameter_lt_one t ht) _) i)
  · rw [sub_apply, familyWordRepresentation_vacuum, dampedWickReconstruction_ou_vacuum t ht]
    apply sub_eq_zero.mpr
    apply lp.ext
    funext w
    exact familyVonNeumannWordCoefficients_OU e he t ht.le T w

/-- Every whole von Neumann algebra operator enters the original norm-closed family algebra at strictly positive time. -/
theorem ouVonNeumannTimeCP_mem_native (e : I → H) (he : Orthonormal ℂ e)
    (t : ℝ) (ht : 0 < t) (T : tensorFamilyDoubleAlgebra e) :
    (ouVonNeumannTimeCP e t ht.le T : TensorFullFock H →L[ℂ] TensorFullFock H) ∈ tensorFamilyAlgebra e := by
  apply (familyWordRepresentation_mem_closed_iff e he _).mp
  rw [familyWordRepresentation_ou_eq_dampedWick e he t ht T]
  exact dampedWickReconstruction_mem_closedAlgebra _ (norm_ouWickParameter_lt_one t ht) _

/-- Genuine state-L2 to operator-norm regularization, with a bound independent of alphabet and ambient Hilbert dimension. -/
theorem norm_ouVonNeumannTimeCP_le_L2 (e : I → H) (he : Orthonormal ℂ e)
    (t : ℝ) (ht : 0 < t) (T : tensorFamilyDoubleAlgebra e) :
    ‖ouVonNeumannTimeCP e t ht.le T‖ ≤
      (1 - Real.exp (-t))⁻¹ ^ 2 * ‖ouVonNeumannVacuumVector e T‖ := by
  rw [← familyWordRepresentation_norm e he, familyWordRepresentation_ou_eq_dampedWick e he t ht T]
  have h := norm_dampedWickReconstruction_apply_le (Real.exp (-t) : ℂ)
    (norm_ouWickParameter_lt_one t ht) (familyVonNeumannWordCoefficients e he T)
  rwa [norm_familyVonNeumannWordCoefficients, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le] at h

end FreeProbability.Fock

import FreeProbability.Fock.OrnsteinUhlenbeckVonNeumannVacuumSymmetry

/-! Exact positive half-time correlations for the actual whole-double-commutant OU map. -/
noncomputable section
open scoped Classical InnerProductSpace ComplexOrder
namespace FreeProbability.Fock
variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The true time-t state correlation equals the squared actual half-time vacuum norm. -/
theorem ouVonNeumannTimeCP_correlation_half_norm (e : I → H) (t : ℝ) (ht : 0 ≤ t)
    (A : tensorFamilyDoubleAlgebra e) :
    (tensorFamilyVonNeumannVacuumState e).expectation (star A * ouVonNeumannTimeCP e t ht A) =
      (‖ouVonNeumannVacuumVector e (ouVonNeumannTimeCP e (t / 2) (div_nonneg ht (by norm_num : (0 : ℝ) ≤ 2)) A)‖ : ℂ) ^ 2 := by
  rw [ouVonNeumannVacuumState_star_mul_inner]
  change inner ℂ ((A : TensorFullFock H →L[ℂ] TensorFullFock H) (tensorVacuum H))
      ((ouVonNeumannTimeCP e t ht A : TensorFullFock H →L[ℂ] TensorFullFock H) (tensorVacuum H)) =
    (‖(ouVonNeumannTimeCP e (t / 2) (div_nonneg ht (by norm_num : (0 : ℝ) ≤ 2)) A :
      TensorFullFock H →L[ℂ] TensorFullFock H) (tensorVacuum H)‖ : ℂ) ^ 2
  rw [ouVonNeumannTimeCP_vacuum_vector, ouVonNeumannTimeCP_vacuum_vector]
  have hh : (degreeDamping H (t / 2) (div_nonneg ht (by norm_num : (0 : ℝ) ≤ 2))).comp
      (degreeDamping H (t / 2) (div_nonneg ht (by norm_num : (0 : ℝ) ≤ 2))) = degreeDamping H t ht := by
    simpa only [add_halves] using degreeDamping_add H (t / 2) (t / 2) (div_nonneg ht (by norm_num : (0 : ℝ) ≤ 2)) (div_nonneg ht (by norm_num : (0 : ℝ) ≤ 2))
  rw [← hh]
  change inner ℂ ((A : TensorFullFock H →L[ℂ] TensorFullFock H) (tensorVacuum H))
    (degreeDamping H (t / 2) (div_nonneg ht (by norm_num : (0 : ℝ) ≤ 2))
      (degreeDamping H (t / 2) (div_nonneg ht (by norm_num : (0 : ℝ) ≤ 2))
        ((A : TensorFullFock H →L[ℂ] TensorFullFock H) (tensorVacuum H)))) = _
  rw [← degreeDamping_inner_symmetric, inner_self_eq_norm_sq_to_K]
  rfl

/-- The correlation is exactly a positive state quadratic form, without any density premise. -/
theorem ouVonNeumannTimeCP_correlation_half_state (e : I → H) (t : ℝ) (ht : 0 ≤ t)
    (A : tensorFamilyDoubleAlgebra e) :
    (tensorFamilyVonNeumannVacuumState e).expectation (star A * ouVonNeumannTimeCP e t ht A) =
      (tensorFamilyVonNeumannVacuumState e).expectation
        (star (ouVonNeumannTimeCP e (t / 2) (div_nonneg ht (by norm_num : (0 : ℝ) ≤ 2)) A) *
          ouVonNeumannTimeCP e (t / 2) (div_nonneg ht (by norm_num : (0 : ℝ) ≤ 2)) A) := by
  rw [ouVonNeumannTimeCP_correlation_half_norm, ouVonNeumannVacuumState_star_self_norm]

 theorem ouVonNeumannTimeCP_correlation_nonneg (e : I → H) (t : ℝ) (ht : 0 ≤ t)
    (A : tensorFamilyDoubleAlgebra e) :
    0 ≤ (tensorFamilyVonNeumannVacuumState e).expectation (star A * ouVonNeumannTimeCP e t ht A) := by
  rw [ouVonNeumannTimeCP_correlation_half_state]
  exact (tensorFamilyVonNeumannVacuumState e).positive _

 theorem ouVonNeumannTimeCP_correlation_le (e : I → H) (t : ℝ) (ht : 0 ≤ t)
    (A : tensorFamilyDoubleAlgebra e) :
    ((tensorFamilyVonNeumannVacuumState e).expectation (star A * ouVonNeumannTimeCP e t ht A)).re ≤
      ((tensorFamilyVonNeumannVacuumState e).expectation (star A * A)).re := by
  rw [ouVonNeumannTimeCP_correlation_half_state]
  exact ouVonNeumannTimeCP_state_L2_le e (t / 2) (div_nonneg ht (by norm_num : (0 : ℝ) ≤ 2)) A

end FreeProbability.Fock

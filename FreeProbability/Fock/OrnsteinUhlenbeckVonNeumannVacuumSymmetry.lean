import FreeProbability.Fock.OrnsteinUhlenbeckVonNeumannVacuumL2

/-! Self-adjoint degree damping and genuine state symmetry on the whole field double commutant. -/
noncomputable section
open scoped Classical InnerProductSpace
namespace FreeProbability.Fock
variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every scalar degree weight is real, so the actual complete Hilbert degree operator is symmetric. -/
theorem degreeDamping_inner_symmetric (t : ℝ) (ht : 0 ≤ t) (f g : TensorFullFock H) :
    inner ℂ (degreeDamping H t ht f) g = inner ℂ f (degreeDamping H t ht g) := by
  simp only [lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  have hw : starRingEnd ℂ (degreeWeight t n) = degreeWeight t n := by
    unfold degreeWeight
    rw [map_pow, Complex.conj_ofReal]
  rw [degreeDamping_degree, degreeDamping_degree, inner_smul_left, inner_smul_right, hw]

/-- Genuine Hilbert adjoint identity on every completed Fock vector. -/
@[simp] theorem degreeDamping_adjoint (t : ℝ) (ht : 0 ≤ t) :
    (degreeDamping H t ht).adjoint = degreeDamping H t ht := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  exact degreeDamping_inner_symmetric t ht

/-- The actual state cross quadratic form is the actual vacuum inner product. -/
theorem ouVonNeumannVacuumState_star_mul_inner (e : I → H) (A B : tensorFamilyDoubleAlgebra e) :
    (tensorFamilyVonNeumannVacuumState e).expectation (star A * B) =
      inner ℂ (ouVonNeumannVacuumVector e A) (ouVonNeumannVacuumVector e B) := by
  change (tensorVacuumState H).expectation
    (star (A : TensorFullFock H →L[ℂ] TensorFullFock H) * B) = _
  rw [tensorVacuumState_expectation, mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  rfl

/-- Exact state symmetry on EVERY pair of whole-double-commutant elements.
No orthonormality or spanning assumption is needed for this identity. -/
theorem ouVonNeumannTimeCP_state_symmetric (e : I → H) (t : ℝ) (ht : 0 ≤ t)
    (A B : tensorFamilyDoubleAlgebra e) :
    (tensorFamilyVonNeumannVacuumState e).expectation (star (ouVonNeumannTimeCP e t ht A) * B) =
      (tensorFamilyVonNeumannVacuumState e).expectation (star A * ouVonNeumannTimeCP e t ht B) := by
  rw [ouVonNeumannVacuumState_star_mul_inner, ouVonNeumannVacuumState_star_mul_inner]
  change inner ℂ
      ((ouVonNeumannTimeCP e t ht A : TensorFullFock H →L[ℂ] TensorFullFock H) (tensorVacuum H))
      ((B : TensorFullFock H →L[ℂ] TensorFullFock H) (tensorVacuum H)) =
    inner ℂ ((A : TensorFullFock H →L[ℂ] TensorFullFock H) (tensorVacuum H))
      ((ouVonNeumannTimeCP e t ht B : TensorFullFock H →L[ℂ] TensorFullFock H) (tensorVacuum H))
  rw [ouVonNeumannTimeCP_vacuum_vector, ouVonNeumannTimeCP_vacuum_vector]
  exact degreeDamping_inner_symmetric t ht _ _

end FreeProbability.Fock

import FreeProbability.Fock.OrnsteinUhlenbeckVonNeumannVacuumIntertwining
import FreeProbability.Fock.TensorFamilyVonNeumannFaithfulness

/-! Actual OU semigroup law on the entire orthonormal-family double commutant.
The proof uses genuine vacuum separation and all-vector degree damping, not a
polynomial-density assumption on the von Neumann algebra. -/
noncomputable section
open scoped Classical InnerProductSpace
namespace FreeProbability.Fock
variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Faithfulness of the actual ON-family state makes the actual tensor vacuum separating. -/
theorem ouVonNeumann_eq_zero_of_vacuum (e : I → H) (he : Orthonormal ℂ e)
    (T : tensorFamilyDoubleAlgebra e)
    (hT : (T : TensorFullFock H →L[ℂ] TensorFullFock H) (tensorVacuum H) = 0) : T = 0 := by
  apply tensorFamilyVonNeumannVacuumState_faithful e he T
  change (tensorVacuumState H).expectation
    (star (T : TensorFullFock H →L[ℂ] TensorFullFock H) *
      (T : TensorFullFock H →L[ℂ] TensorFullFock H)) = 0
  rw [tensorVacuumState_expectation, mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, hT, inner_zero_left]

/-- Equality on the genuine vacuum determines any two operators in this literal double commutant. -/
theorem ouVonNeumann_vacuum_ext (e : I → H) (he : Orthonormal ℂ e)
    (T S : tensorFamilyDoubleAlgebra e)
    (h : (T : TensorFullFock H →L[ℂ] TensorFullFock H) (tensorVacuum H) =
      (S : TensorFullFock H →L[ℂ] TensorFullFock H) (tensorVacuum H)) : T = S := by
  apply sub_eq_zero.mp
  apply ouVonNeumann_eq_zero_of_vacuum e he (T - S)
  change (T : TensorFullFock H →L[ℂ] TensorFullFock H) (tensorVacuum H) -
    (S : TensorFullFock H →L[ℂ] TensorFullFock H) (tensorVacuum H) = 0
  rw [h, sub_self]

/-- Genuine additive-time composition on EVERY element of the whole prescribed ON-family algebra. -/
theorem ouVonNeumannTimeCP_add (e : I → H) (he : Orthonormal ℂ e)
    (t u : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) (T : tensorFamilyDoubleAlgebra e) :
    ouVonNeumannTimeCP e t ht (ouVonNeumannTimeCP e u hu T) =
      ouVonNeumannTimeCP e (t + u) (add_nonneg ht hu) T := by
  apply ouVonNeumann_vacuum_ext e he
  rw [ouVonNeumannTimeCP_vacuum_vector, ouVonNeumannTimeCP_vacuum_vector,
    ouVonNeumannTimeCP_vacuum_vector]
  exact DFunLike.congr_fun (degreeDamping_add H t u ht hu)
    ((T : TensorFullFock H →L[ℂ] TensorFullFock H) (tensorVacuum H))

/-- Actual bounded-linear semigroup identity on the complete double-commutant C-star algebra. -/
theorem ouVonNeumannTimeContinuous_add (e : I → H) (he : Orthonormal ℂ e)
    (t u : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    (ouVonNeumannTimeContinuous e t ht).comp (ouVonNeumannTimeContinuous e u hu) =
      ouVonNeumannTimeContinuous e (t + u) (add_nonneg ht hu) := by
  apply ContinuousLinearMap.ext
  intro T
  exact ouVonNeumannTimeCP_add e he t u ht hu T

end FreeProbability.Fock

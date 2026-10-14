import FreeProbability.Fock.OrnsteinUhlenbeckFamilyCyclicBasisDamping

/-! Genuine complete original-family word coefficients for EVERY whole-double-commutant operator. -/
noncomputable section
open scoped Classical InnerProductSpace
namespace FreeProbability.Fock
variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Actual bounded whole-algebra vacuum coefficients in the ORIGINAL complete family word basis. -/
def familyVonNeumannWordCoefficients (e : I → H) (he : Orthonormal ℂ e) :
    tensorFamilyDoubleAlgebra e →L[ℂ] WordSpace I :=
  (familyCyclicWordUnitary e he).symm.toLinearIsometry.toContinuousLinearMap.comp
    (ouVonNeumannCyclicVector e)

/-- These genuine square-summable coefficients recover the same actual cyclic vacuum vector. -/
theorem familyCyclicWordUnitary_coefficients (e : I → H) (he : Orthonormal ℂ e)
    (T : tensorFamilyDoubleAlgebra e) :
    familyCyclicWordUnitary e he (familyVonNeumannWordCoefficients e he T) = ouVonNeumannCyclicVector e T :=
  (familyCyclicWordUnitary e he).apply_symm_apply _

 theorem familyVonNeumannWordCoefficients_injective (e : I → H) (he : Orthonormal ℂ e) :
    Function.Injective (familyVonNeumannWordCoefficients e he) := by
  intro T S h
  apply ouVonNeumannCyclicVector_injective e he
  exact (familyCyclicWordUnitary e he).symm.injective h

 theorem norm_familyVonNeumannWordCoefficients (e : I → H) (he : Orthonormal ℂ e)
    (T : tensorFamilyDoubleAlgebra e) :
    ‖familyVonNeumannWordCoefficients e he T‖ = ‖ouVonNeumannVacuumVector e T‖ := by
  change ‖(familyCyclicWordUnitary e he).symm (ouVonNeumannCyclicVector e T)‖ = _
  rw [LinearIsometryEquiv.norm_map]
  rfl

theorem norm_familyVonNeumannWordCoefficients_le (e : I → H) (he : Orthonormal ℂ e)
    (T : tensorFamilyDoubleAlgebra e) : ‖familyVonNeumannWordCoefficients e he T‖ ≤ ‖T‖ := by
  rw [norm_familyVonNeumannWordCoefficients]
  have ht := (T : TensorFullFock H →L[ℂ] TensorFullFock H).le_opNorm (tensorVacuum H)
  rw [norm_tensorVacuum, mul_one] at ht
  exact ht

/-- The empty-word coefficient is exactly the genuine prescribed-family vacuum expectation. -/
theorem familyVonNeumannWordCoefficients_nil (e : I → H) (he : Orthonormal ℂ e)
    (T : tensorFamilyDoubleAlgebra e) :
    familyVonNeumannWordCoefficients e he T [] = (tensorFamilyVonNeumannVacuumState e).expectation T := by
  change (familyCyclicBasis e he).repr (ouVonNeumannCyclicVector e T) [] = _
  rw [HilbertBasis.repr_apply_apply, familyCyclicBasis_apply, familyCyclicWord_nil]
  change inner ℂ (tensorVacuum H) ((T : TensorFullFock H →L[ℂ] TensorFullFock H) (tensorVacuum H)) =
    (tensorVacuumState H).expectation T
  exact (tensorVacuumState_expectation H (T : TensorFullFock H →L[ℂ] TensorFullFock H)).symm

/-- Exact faithful-state quadratic norm of every whole-algebra coefficient vector. -/
theorem familyVonNeumannWordCoefficients_state_norm (e : I → H) (he : Orthonormal ℂ e)
    (T : tensorFamilyDoubleAlgebra e) :
    (tensorFamilyVonNeumannVacuumState e).expectation (star T * T) =
      (‖familyVonNeumannWordCoefficients e he T‖ : ℂ) ^ 2 := by
  rw [norm_familyVonNeumannWordCoefficients]
  exact ouVonNeumannVacuumState_star_self_norm e T

/-- The actual state inner product agrees with the complete original-word coefficient inner product. -/
theorem familyVonNeumannWordCoefficients_state_inner (e : I → H) (he : Orthonormal ℂ e)
    (T S : tensorFamilyDoubleAlgebra e) :
    (tensorFamilyVonNeumannVacuumState e).expectation (star T * S) =
      inner ℂ (familyVonNeumannWordCoefficients e he T) (familyVonNeumannWordCoefficients e he S) := by
  change (tensorFamilyVonNeumannVacuumState e).expectation (star T * S) =
    inner ℂ ((familyCyclicWordUnitary e he).symm (ouVonNeumannCyclicVector e T))
      ((familyCyclicWordUnitary e he).symm (ouVonNeumannCyclicVector e S))
  rw [LinearIsometryEquiv.inner_map_map]
  change (tensorVacuumState H).expectation
    (star (T : TensorFullFock H →L[ℂ] TensorFullFock H) * S) =
      inner ℂ ((T : TensorFullFock H →L[ℂ] TensorFullFock H) (tensorVacuum H))
        ((S : TensorFullFock H →L[ℂ] TensorFullFock H) (tensorVacuum H))
  rw [tensorVacuumState_expectation, mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]

/-- Genuine unconditional cyclic vacuum expansion for EVERY whole-double-commutant element. -/
theorem hasSum_familyVonNeumannWordCoefficients (e : I → H) (he : Orthonormal ℂ e)
    (T : tensorFamilyDoubleAlgebra e) :
    HasSum (fun w => familyVonNeumannWordCoefficients e he T w • familyCyclicWord e w)
      (ouVonNeumannCyclicVector e T) := hasSum_familyCyclicWord e he _

/-- Actual whole-algebra OU has exactly the original-family length multiplier at every word coefficient. -/
theorem familyVonNeumannWordCoefficients_OU (e : I → H) (he : Orthonormal ℂ e) (t : ℝ) (ht : 0 ≤ t)
    (T : tensorFamilyDoubleAlgebra e) (w : List I) :
    familyVonNeumannWordCoefficients e he (ouVonNeumannTimeCP e t ht T) w =
      degreeWeight t w.length • familyVonNeumannWordCoefficients e he T w := by
  change (familyCyclicWordUnitary e he).symm (ouVonNeumannCyclicVector e (ouVonNeumannTimeCP e t ht T)) w = _
  rw [← familyOUL2_ouVonNeumannCyclicVector e he t ht T]
  exact familyOUL2_word_coefficient e he t ht _ w

@[simp] theorem familyVonNeumannWordCoefficients_Wick (e : I → H) (he : Orthonormal ℂ e) (w : List I) :
    familyVonNeumannWordCoefficients e he (ouCyclicNativeInclusion e (familyClosedWick e w)) = word w := by
  apply (familyCyclicWordUnitary e he).injective
  rw [familyCyclicWordUnitary_coefficients, ouVonNeumannCyclicVector_native, familyCyclicWordUnitary_word]
  rfl

end FreeProbability.Fock

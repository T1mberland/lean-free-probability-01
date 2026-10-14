import FreeProbability.Fock.OrnsteinUhlenbeckVonNeumannIntrinsicCP
import FreeProbability.Fock.OrnsteinUhlenbeckVonNeumannRangeTime

/-! Nonnegative-time intrinsic CP contractions and actual time-zero identity.
No additive semigroup law or order-supremum normality is asserted here. -/
noncomputable section
open scoped Classical CStarAlgebra
namespace FreeProbability.Fock
attribute [local irreducible] fullFockTensorDecomposition isometryPrefixTargetUnitary
  isometrySuffixEmbedding wordSuffixEmbedding doubledRotation secondQuantization isometryPrefixEmbedding
  doubledFockRotation doubledFirst doubledSecond fullFockBasis tensorCreation tensorAnnihilation tensorFamilyField
variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Genuine intrinsic CP map at each nonnegative time on the actual family double commutant. -/
def ouVonNeumannTimeCP (e : I → H) (t : ℝ) (ht : 0 ≤ t) :
    tensorFamilyDoubleAlgebra e →CP tensorFamilyDoubleAlgebra e :=
  ouVonNeumannCP e (ouCosine t) (ouSine t) (ouRotation_parameters t ht)

@[simp] theorem ouVonNeumannTimeCP_coe (e : I → H) (t : ℝ) (ht : 0 ≤ t)
    (T : tensorFamilyDoubleAlgebra e) :
    (ouVonNeumannTimeCP e t ht T : TensorFullFock H →L[ℂ] TensorFullFock H) =
      ouDoubleCommutantTimeCP (H := H) t ht T := rfl

@[simp] theorem ouVonNeumannTimeCP_one (e : I → H) (t : ℝ) (ht : 0 ≤ t) :
    ouVonNeumannTimeCP e t ht 1 = 1 :=
  ouVonNeumannCP_one e _ _ _

 theorem norm_ouVonNeumannTimeCP_le (e : I → H) (t : ℝ) (ht : 0 ≤ t)
    (T : tensorFamilyDoubleAlgebra e) : ‖ouVonNeumannTimeCP e t ht T‖ ≤ ‖T‖ :=
  norm_ouVonNeumannCP_le e _ _ _ T

 theorem ouVonNeumannTimeCP_expectation (e : I → H) (t : ℝ) (ht : 0 ≤ t)
    (T : tensorFamilyDoubleAlgebra e) :
    (tensorFamilyVonNeumannVacuumState e).expectation (ouVonNeumannTimeCP e t ht T) =
      (tensorFamilyVonNeumannVacuumState e).expectation T :=
  ouVonNeumannCP_expectation e _ _ _ T

/-- Time zero fixes every element of the literal double commutant, not merely polynomials. -/
@[simp] theorem ouVonNeumannTimeCP_zero (e : I → H) (T : tensorFamilyDoubleAlgebra e) :
    ouVonNeumannTimeCP e 0 (le_refl 0) T = T := by
  apply Subtype.ext
  change ouDoubleCommutantTimeCP (H := H) 0 (le_refl 0)
    (T : TensorFullFock H →L[ℂ] TensorFullFock H) = T
  exact ouDoubleCommutantTimeCP_zero (T : TensorFullFock H →L[ℂ] TensorFullFock H)

/-- Bounded linear realization on the actual complete intrinsic C-star algebra. -/
def ouVonNeumannTimeContinuous (e : I → H) (t : ℝ) (ht : 0 ≤ t) :
    tensorFamilyDoubleAlgebra e →L[ℂ] tensorFamilyDoubleAlgebra e :=
  (ouVonNeumannTimeCP e t ht).toLinearMap.mkContinuous 1 (by
    intro T
    change ‖ouVonNeumannTimeCP e t ht T‖ ≤ 1 * ‖T‖
    rw [one_mul]
    exact norm_ouVonNeumannTimeCP_le e t ht T)

@[simp] theorem ouVonNeumannTimeContinuous_apply (e : I → H) (t : ℝ) (ht : 0 ≤ t)
    (T : tensorFamilyDoubleAlgebra e) :
    ouVonNeumannTimeContinuous e t ht T = ouVonNeumannTimeCP e t ht T := rfl

 theorem norm_ouVonNeumannTimeContinuous_le (e : I → H) (t : ℝ) (ht : 0 ≤ t) :
    ‖ouVonNeumannTimeContinuous e t ht‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro T
  simpa using norm_ouVonNeumannTimeCP_le e t ht T

end FreeProbability.Fock

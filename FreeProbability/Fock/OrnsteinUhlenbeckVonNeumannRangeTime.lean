import FreeProbability.Fock.OrnsteinUhlenbeckVonNeumannRangeCP
import FreeProbability.Fock.SecondQuantizationFunctor

/-! # Actual nonnegative-time double-commutant OU maps and ALL-operator time-zero identity

The additive semigroup law and positive-supremum normality remain separate.
-/
noncomputable section
open scoped Classical CStarAlgebra
namespace FreeProbability.Fock
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- The actual real rotation at parameters (1,0) is the identity on the doubled Hilbert space. -/
theorem ouRange_rotation_one_zero (hrs : (1 : ℝ) ^ 2 + 0 ^ 2 = 1) :
    doubledRotation (H := H) 1 0 hrs = LinearIsometryEquiv.refl ℂ (DoubledHilbert H) := by
  apply LinearIsometryEquiv.ext
  intro x
  apply WithLp.ofLp_injective 2
  apply Prod.ext <;> simp [doubledRotation, doubledRotationLinear]

/-- The actual full Fock rotation at (1,0) is identity. -/
theorem ouRange_fockRotation_one_zero (hrs : (1 : ℝ) ^ 2 + 0 ^ 2 = 1) :
    doubledFockRotation H 1 0 hrs = LinearIsometryEquiv.refl ℂ (TensorFullFock (DoubledHilbert H)) := by
  change secondQuantization (doubledRotation (H := H) 1 0 hrs) = _
  rw [ouRange_rotation_one_zero, secondQuantization_refl]

/-- ALL bounded operators are fixed at zero noise, using the actual Γ-compression left inverse. -/
theorem ouDoubleCommutantRawCP_one_zero (hrs : (1 : ℝ) ^ 2 + 0 ^ 2 = 1)
    (T : TensorFullFock H →L[ℂ] TensorFullFock H) : ouDoubleCommutantRawCP 1 0 hrs T = T := by
  rw [ouDoubleCommutantRawCP_apply, rotatedFockCompression_apply, ouRange_fockRotation_one_zero]
  exact isometryPrefixEmbedding_compression (doubledFirst H) T

/-- Actual CP map at t≥0; source is ALL bounded Fock operators and literal DC range is proved below. -/
def ouDoubleCommutantTimeCP (t : ℝ) (ht : 0 ≤ t) :
    (TensorFullFock H →L[ℂ] TensorFullFock H) →CP (TensorFullFock H →L[ℂ] TensorFullFock H) :=
  ouDoubleCommutantRawCP (ouCosine t) (ouSine t) (ouRotation_parameters t ht)

@[simp] theorem ouDoubleCommutantTimeCP_one (t : ℝ) (ht : 0 ≤ t) :
    ouDoubleCommutantTimeCP (H := H) t ht 1 = 1 := ouDoubleCommutantRawCP_one _ _ _

theorem norm_ouDoubleCommutantTimeCP_le (t : ℝ) (ht : 0 ≤ t)
    (T : TensorFullFock H →L[ℂ] TensorFullFock H) :
    ‖ouDoubleCommutantTimeCP t ht T‖ ≤ ‖T‖ := norm_ouDoubleCommutantRawCP_le _ _ _ T

theorem ouDoubleCommutantTimeCP_vacuum_expectation (t : ℝ) (ht : 0 ≤ t)
    (T : TensorFullFock H →L[ℂ] TensorFullFock H) :
    (tensorVacuumState H).expectation (ouDoubleCommutantTimeCP t ht T) = (tensorVacuumState H).expectation T :=
  ouDoubleCommutantRawCP_vacuum_expectation _ _ _ T

theorem ouDoubleCommutantTimeCP_mem_familyDoubleCentralizer {I : Type*} (t : ℝ) (ht : 0 ≤ t)
    (e : I → H) {T : TensorFullFock H →L[ℂ] TensorFullFock H}
    (hT : T ∈ Set.centralizer (Set.centralizer (Set.range (tensorFamilyField e)))) :
    ouDoubleCommutantTimeCP t ht T ∈ Set.centralizer (Set.centralizer (Set.range (tensorFamilyField e))) :=
  ouDoubleCommutantRawCP_mem_familyDoubleCentralizer _ _ _ e hT

/-- Genuine time-zero identity for EVERY bounded source operator, not only Wick polynomials. -/
theorem ouDoubleCommutantTimeCP_zero (T : TensorFullFock H →L[ℂ] TensorFullFock H) :
    ouDoubleCommutantTimeCP 0 (le_refl 0) T = T := by
  unfold ouDoubleCommutantTimeCP
  simpa only [ouCosine, neg_zero, Real.exp_zero, ouSine, one_pow, sub_self, Real.sqrt_zero] using
    (ouDoubleCommutantRawCP_one_zero (H := H) (by norm_num) T)

end FreeProbability.Fock

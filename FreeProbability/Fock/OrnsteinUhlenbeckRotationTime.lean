import FreeProbability.Fock.OrnsteinUhlenbeckDilation
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Standard nonnegative-time parameters for the actual Fock rotation dilation -/
noncomputable section
open scoped InnerProductSpace CStarAlgebra
namespace FreeProbability.Fock

/-- The real contraction coefficient at time t. -/
def ouCosine (t : ℝ) : ℝ := Real.exp (-t)

/-- The real complementary noise coefficient, with nonnegative square root. -/
def ouSine (t : ℝ) : ℝ := Real.sqrt (1 - ouCosine t ^ 2)

@[simp] theorem ouCosine_pos (t : ℝ) : 0 < ouCosine t := Real.exp_pos _

theorem ouCosine_le_one (t : ℝ) (ht : 0 ≤ t) : ouCosine t ≤ 1 :=
  Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)

theorem ouRotation_parameters (t : ℝ) (ht : 0 ≤ t) : ouCosine t ^ 2 + ouSine t ^ 2 = 1 := by
  have hp := ouCosine_pos t
  have hb := ouCosine_le_one t ht
  have hs : 0 ≤ 1 - ouCosine t ^ 2 := by nlinarith
  rw [ouSine, Real.sq_sqrt hs]
  ring

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Actual doubled-Hilbert unitary with r=e⁻ᵗ and s=√(1−e⁻²ᵗ). -/
def ouTimeRotation (t : ℝ) (ht : 0 ≤ t) :
    DoubledHilbert H ≃ₗᵢ[ℂ] DoubledHilbert H :=
  doubledRotation (ouCosine t) (ouSine t) (ouRotation_parameters t ht)

/-- Actual unital CP dilation map at nonnegative time, on doubled Fock bounded operators.
This is not yet asserted to restrict to the desired generated-algebra OU semigroup. -/
def ouTimeDilation (t : ℝ) (ht : 0 ≤ t) :
    (TensorFullFock (DoubledHilbert H) →L[ℂ] TensorFullFock (DoubledHilbert H)) →CP
      (TensorFullFock H →L[ℂ] TensorFullFock H) :=
  rotatedFockCompression H (ouCosine t) (ouSine t) (ouRotation_parameters t ht)

@[simp] theorem ouTimeDilation_one (t : ℝ) (ht : 0 ≤ t) : ouTimeDilation H t ht 1 = 1 :=
  rotatedFockCompression_one H _ _ _

theorem norm_ouTimeDilation_le (t : ℝ) (ht : 0 ≤ t)
    (T : TensorFullFock (DoubledHilbert H) →L[ℂ] TensorFullFock (DoubledHilbert H)) :
    ‖ouTimeDilation H t ht T‖ ≤ ‖T‖ := norm_rotatedFockCompression_le H _ _ _ T

theorem ouTimeDilation_vacuum_expectation (t : ℝ) (ht : 0 ≤ t)
    (T : TensorFullFock (DoubledHilbert H) →L[ℂ] TensorFullFock (DoubledHilbert H)) :
    inner ℂ (tensorVacuum H) (ouTimeDilation H t ht T (tensorVacuum H)) =
      inner ℂ (tensorVacuum (DoubledHilbert H)) (T (tensorVacuum (DoubledHilbert H))) :=
  rotatedFockCompression_vacuum_expectation H _ _ _ T

end FreeProbability.Fock

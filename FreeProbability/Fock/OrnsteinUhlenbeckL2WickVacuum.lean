import FreeProbability.Fock.OrnsteinUhlenbeckL2Damping

/-! # Actual recursive Wick vacuum vectors occupy their true completed tensor degree -/
noncomputable section
open scoped Classical InnerProductSpace TensorProduct
open UniformSpace
namespace FreeProbability.Fock
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The literal completed pure tensor corresponding to an original-vector word. -/
def tensorWordVector : (w : List H) → TensorPower H w.length
  | [] => tensorPowerZero H 1
  | h :: w => ((h ⊗ₜ[ℂ] tensorWordVector w : H ⊗[ℂ] TensorPower H w.length) :
      Completion (H ⊗[ℂ] TensorPower H w.length))

/-- The actual creator-word vacuum image is exactly a vector in its completed tensor degree. -/
theorem tensorCreatorWord_vacuum_degree (w : List H) :
    tensorCreatorWord w (tensorVacuum H) = lp.single 2 w.length (tensorWordVector w) := by
  induction w with
  | nil => rfl
  | cons h w ih =>
    change tensorCreation H h (tensorCreatorWord w (tensorVacuum H)) = _
    rw [ih]
    exact tensorCreation_single H w.length h (tensorWordVector w)

/-- The recursive Wick polynomial has exactly its pure creator vacuum vector. -/
theorem tensorVectorWick_vacuum_creator (w : List H) :
    tensorVectorWick w (tensorVacuum H) = tensorCreatorWord w (tensorVacuum H) := by
  induction w using List.twoStepInduction with
  | nil => rfl
  | singleton h =>
    simp [tensorVectorWick, tensorCreatorWord]
  | cons_cons h k w hw hkw =>
    have ha := DFunLike.congr_fun (tensorAnnihilation_creation H h k)
      (tensorCreatorWord w (tensorVacuum H))
    change tensorAnnihilation H h (tensorCreatorWord (k :: w) (tensorVacuum H)) =
      inner ℂ h k • tensorCreatorWord w (tensorVacuum H) at ha
    change ((tensorCreation H h + tensorAnnihilation H h) * tensorVectorWick (k :: w) -
      inner ℂ h k • tensorVectorWick w) (tensorVacuum H) =
      tensorCreation H h (tensorCreatorWord (k :: w) (tensorVacuum H))
    rw [sub_apply, mul_apply_eq_comp, smul_apply, add_apply, hkw k, hw, ha]
    exact add_sub_cancel_right _ _

/-- Pure-degree identification for every genuine vector Wick polynomial, without ON assumptions. -/
theorem tensorVectorWick_vacuum_degree (w : List H) :
    tensorVectorWick w (tensorVacuum H) = lp.single 2 w.length (tensorWordVector w) :=
  (tensorVectorWick_vacuum_creator w).trans (tensorCreatorWord_vacuum_degree w)

/-- Actual degree damping acts on each recursive Wick vacuum image by the exact OU eigenvalue. -/
theorem degreeDamping_Wick_vacuum (t : ℝ) (ht : 0 ≤ t) (w : List H) :
    degreeDamping H t ht (tensorVectorWick w (tensorVacuum H)) =
      degreeWeight t w.length • tensorVectorWick w (tensorVacuum H) := by
  rw [tensorVectorWick_vacuum_degree, degreeDamping_single]

variable {I : Type*}
/-- The actual closed family Wick vector is damped by its literal word degree. -/
theorem degreeDamping_familyClosedWick_vacuum (e : I → H) (t : ℝ) (ht : 0 ≤ t) (w : List I) :
    degreeDamping H t ht ((familyClosedWick e w : TensorFullFock H →L[ℂ] TensorFullFock H) (tensorVacuum H)) =
      (Real.exp (-t) : ℂ) ^ w.length •
        (familyClosedWick e w : TensorFullFock H →L[ℂ] TensorFullFock H) (tensorVacuum H) := by
  have hd := degreeDamping_Wick_vacuum t ht (w.map e)
  rw [List.length_map] at hd
  exact hd

end FreeProbability.Fock

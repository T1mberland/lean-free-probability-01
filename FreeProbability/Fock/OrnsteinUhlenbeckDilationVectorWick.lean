import FreeProbability.Fock.OrnsteinUhlenbeckDilationNormalOrder

/-! # Genuine recursive vector Wick operators and their normal-order expansion -/
noncomputable section
open scoped Classical InnerProductSpace
namespace FreeProbability.Fock
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Genuine Wick recursion on arbitrary original one-particle vectors. -/
def tensorVectorWick : List H → (TensorFullFock H →L[ℂ] TensorFullFock H)
  | [] => 1
  | h :: w => (tensorCreation H h + tensorAnnihilation H h) * tensorVectorWick w -
      match w with
      | [] => 0
      | k :: v => inner ℂ h k • tensorVectorWick v

@[simp] theorem tensorNormalOrder_nil : tensorNormalOrder ([] : List H) = 1 := by
  simp [tensorNormalOrder]

theorem tensorNormalOrder_cons (h : H) (w : List H) :
    tensorNormalOrder (h :: w) = tensorCreation H h * tensorNormalOrder w +
      tensorAnnihilation H h * tensorAnnihilatorWord w := by
  unfold tensorNormalOrder
  simp only [List.length_cons]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, List.take_zero, tensorCreatorWord_nil, one_mul,
    List.drop_zero, tensorAnnihilatorWord_cons, List.take_succ_cons, tensorCreatorWord_cons,
    List.drop_succ_cons]
  rw [Finset.mul_sum]
  simp only [mul_assoc]
  abel

theorem annihilation_tensorNormalOrder_cons (h k : H) (w : List H) :
    tensorAnnihilation H h * tensorNormalOrder (k :: w) =
      inner ℂ h k • tensorNormalOrder w +
        tensorAnnihilation H h * tensorAnnihilatorWord (k :: w) := by
  rw [tensorNormalOrder_cons, mul_add, ← mul_assoc, tensorAnnihilation_creation]
  have hm : (inner ℂ h k • (1 : TensorFullFock H →L[ℂ] TensorFullFock H)) * tensorNormalOrder w =
      inner ℂ h k • tensorNormalOrder w := by
    apply ContinuousLinearMap.ext
    intro f
    simp
  rw [hm]
  rfl

/-- Every recursive vector Wick polynomial equals the literal all-cut bounded operator sum. -/
theorem tensorVectorWick_eq_normalOrder (w : List H) : tensorVectorWick w = tensorNormalOrder w := by
  induction w using List.twoStepInduction with
  | nil => simp [tensorVectorWick]
  | singleton h => simp [tensorVectorWick, tensorNormalOrder_cons]
  | cons_cons h k w h₁ h₂ =>
    change (tensorCreation H h + tensorAnnihilation H h) * tensorVectorWick (k :: w) -
      inner ℂ h k • tensorVectorWick w = _
    rw [h₂ k, h₁, add_mul, annihilation_tensorNormalOrder_cons, tensorNormalOrder_cons h (k :: w)]
    abel

/-- Actual compression of the rotated recursive Wick operator has exact total degree scaling. -/
theorem rotated_tensorVectorWick_compression (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1) (w : List H) :
    secondQuantizationCompression (doubledFirst H) (tensorVectorWick (rotatedFirstWord r s hrs w)) =
      (r : ℂ) ^ w.length • tensorVectorWick w := by
  rw [tensorVectorWick_eq_normalOrder, tensorVectorWick_eq_normalOrder,
    rotated_tensorNormalOrder_compression]

end FreeProbability.Fock

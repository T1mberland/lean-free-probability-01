import FreeProbability.Fock.OrnsteinUhlenbeckDilationIntertwining

/-! # Actual word projection in the real rotation dilation -/
noncomputable section
open scoped Classical InnerProductSpace
namespace FreeProbability.Fock
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Actual ordered creator product for arbitrary one-particle vectors. -/
def tensorCreatorWord (w : List H) : TensorFullFock H →L[ℂ] TensorFullFock H :=
  (w.map (tensorCreation H)).prod

/-- Actual ordered annihilator product for arbitrary one-particle vectors. -/
def tensorAnnihilatorWord (w : List H) : TensorFullFock H →L[ℂ] TensorFullFock H :=
  (w.map (tensorAnnihilation H)).prod

@[simp] theorem tensorCreatorWord_nil : tensorCreatorWord ([] : List H) = 1 := rfl
@[simp] theorem tensorCreatorWord_cons (h : H) (w : List H) :
    tensorCreatorWord (h :: w) = tensorCreation H h * tensorCreatorWord w := rfl
@[simp] theorem tensorAnnihilatorWord_nil : tensorAnnihilatorWord ([] : List H) = 1 := rfl
@[simp] theorem tensorAnnihilatorWord_cons (h : H) (w : List H) :
    tensorAnnihilatorWord (h :: w) = tensorAnnihilation H h * tensorAnnihilatorWord w := rfl

/-- Rotation of all included one-particle vectors, preserving their order. -/
def rotatedFirstWord (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1) (w : List H) : List (DoubledHilbert H) :=
  w.map (fun h => doubledRotation r s hrs (doubledFirst H h))

/-- Exact left creator projection, for every doubled-Fock vector. -/
theorem rotated_creator_left_projection (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1)
    (h : H) (f : TensorFullFock (DoubledHilbert H)) :
    (doubledFockInclusion H).toContinuousLinearMap.adjoint
      (tensorCreation (DoubledHilbert H) (doubledRotation r s hrs (doubledFirst H h)) f) =
      (r : ℂ) • tensorCreation H h ((doubledFockInclusion H).toContinuousLinearMap.adjoint f) := by
  have hi := DFunLike.congr_fun (inclusion_adjoint_creation_comp (doubledFirst H) h) f
  have hn := congrArg ContinuousLinearMap.adjoint
    (orthogonal_tensorAnnihilation_inclusion (doubledFirst H) (doubledSecond H h)
      (doubled_noise_orthogonal h))
  simp only [ContinuousLinearMap.adjoint_comp, tensorAnnihilation,
    ContinuousLinearMap.adjoint_adjoint, map_zero] at hn
  have hnf := DFunLike.congr_fun hn f
  change (doubledFockInclusion H).toContinuousLinearMap.adjoint
    (tensorCreation (DoubledHilbert H) (doubledSecond H h) f) = 0 at hnf
  rw [doubledRotation_first, ou_tensorCreation_add, ou_tensorCreation_smul, ou_tensorCreation_smul]
  change (doubledFockInclusion H).toContinuousLinearMap.adjoint
    ((r : ℂ) • tensorCreation (DoubledHilbert H) (doubledFirst H h) f +
      (s : ℂ) • tensorCreation (DoubledHilbert H) (doubledSecond H h) f) = _
  rw [map_add, map_smul, map_smul, hnf, smul_zero, add_zero]
  exact congrArg ((r : ℂ) • ·) hi

/-- Annihilation of a real linear combination is the same real linear combination of adjoints. -/
theorem ou_tensorAnnihilation_real_add (r s : ℝ) (a b : DoubledHilbert H) :
    tensorAnnihilation (DoubledHilbert H) ((r : ℂ) • a + (s : ℂ) • b) =
      (r : ℂ) • tensorAnnihilation (DoubledHilbert H) a +
        (s : ℂ) • tensorAnnihilation (DoubledHilbert H) b := by
  change star (tensorCreation (DoubledHilbert H) ((r : ℂ) • a + (s : ℂ) • b)) = _
  rw [ou_tensorCreation_add, ou_tensorCreation_smul, ou_tensorCreation_smul]
  change ((r : ℂ) • tensorCreation (DoubledHilbert H) a +
    (s : ℂ) • tensorCreation (DoubledHilbert H) b).adjoint = _
  rw [map_add, map_smulₛₗ, map_smulₛₗ]
  have hr : starRingEnd ℂ (r : ℂ) = (r : ℂ) := Complex.conj_ofReal r
  have hs : starRingEnd ℂ (s : ℂ) = (s : ℂ) := Complex.conj_ofReal s
  rw [hr, hs]
  rfl


/-- Exact right annihilator projection, for every original-Fock vector. -/
theorem rotated_annihilator_right_projection (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1)
    (h : H) (f : TensorFullFock H) :
    tensorAnnihilation (DoubledHilbert H) (doubledRotation r s hrs (doubledFirst H h))
      (doubledFockInclusion H f) =
        (r : ℂ) • doubledFockInclusion H (tensorAnnihilation H h f) := by
  have hi := DFunLike.congr_fun (inclusion_annihilation_comp (doubledFirst H) h) f
  have hn := DFunLike.congr_fun (doubled_noise_annihilation_inclusion h) f
  change tensorAnnihilation (DoubledHilbert H) (doubledSecond H h) (doubledFockInclusion H f) = 0 at hn
  rw [doubledRotation_first, ou_tensorAnnihilation_real_add]
  change (r : ℂ) • tensorAnnihilation (DoubledHilbert H) (doubledFirst H h)
    (doubledFockInclusion H f) + (s : ℂ) • tensorAnnihilation (DoubledHilbert H) (doubledSecond H h)
      (doubledFockInclusion H f) = _
  rw [hn, smul_zero, add_zero]
  exact congrArg ((r : ℂ) • ·) hi

/-- Full creator-word projection with the exact length exponent. -/
theorem rotated_creatorWord_left_projection (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1)
    (w : List H) (f : TensorFullFock (DoubledHilbert H)) :
    (doubledFockInclusion H).toContinuousLinearMap.adjoint
      (tensorCreatorWord (rotatedFirstWord r s hrs w) f) =
      (r : ℂ) ^ w.length • tensorCreatorWord w
        ((doubledFockInclusion H).toContinuousLinearMap.adjoint f) := by
  induction w generalizing f with
  | nil => simp [rotatedFirstWord]
  | cons h w ih =>
    simp only [rotatedFirstWord, List.map_cons, tensorCreatorWord_cons, mul_apply_eq_comp]
    change (doubledFockInclusion H).toContinuousLinearMap.adjoint
      (tensorCreation (DoubledHilbert H) (doubledRotation r s hrs (doubledFirst H h))
        (tensorCreatorWord (rotatedFirstWord r s hrs w) f)) = _
    rw [rotated_creator_left_projection, ih, map_smul, smul_smul]
    simp only [List.length_cons, pow_succ']

/-- Full annihilator-word projection with the exact length exponent. -/
theorem rotated_annihilatorWord_right_projection (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1)
    (w : List H) (f : TensorFullFock H) :
    tensorAnnihilatorWord (rotatedFirstWord r s hrs w) (doubledFockInclusion H f) =
      (r : ℂ) ^ w.length • doubledFockInclusion H (tensorAnnihilatorWord w f) := by
  induction w generalizing f with
  | nil => simp [rotatedFirstWord]
  | cons h w ih =>
    simp only [rotatedFirstWord, List.map_cons, tensorAnnihilatorWord_cons, mul_apply_eq_comp]
    change tensorAnnihilation (DoubledHilbert H) (doubledRotation r s hrs (doubledFirst H h))
      (tensorAnnihilatorWord (rotatedFirstWord r s hrs w) (doubledFockInclusion H f)) = _
    rw [ih, map_smul, rotated_annihilator_right_projection, smul_smul]
    simp only [List.length_cons, pow_succ, mul_comm]

end FreeProbability.Fock

import FreeProbability.Fock.OrnsteinUhlenbeckDilationWords

/-! # True all-cut normal-order compression under the Fock rotation -/
noncomputable section
open scoped Classical InnerProductSpace
namespace FreeProbability.Fock
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Actual normal-ordered creator/annihilator cut, at arbitrary vector degree. -/
theorem rotated_normalOrder_cut_compression (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1)
    (u v : List H) :
    secondQuantizationCompression (doubledFirst H)
      (tensorCreatorWord (rotatedFirstWord r s hrs u) *
        tensorAnnihilatorWord (rotatedFirstWord r s hrs v)) =
      (r : ℂ) ^ (u.length + v.length) • (tensorCreatorWord u * tensorAnnihilatorWord v) := by
  apply ContinuousLinearMap.ext
  intro f
  change (doubledFockInclusion H).toContinuousLinearMap.adjoint
    (tensorCreatorWord (rotatedFirstWord r s hrs u)
      (tensorAnnihilatorWord (rotatedFirstWord r s hrs v) (doubledFockInclusion H f))) =
      (r : ℂ) ^ (u.length + v.length) • tensorCreatorWord u (tensorAnnihilatorWord v f)
  rw [rotated_annihilatorWord_right_projection, map_smul, map_smul,
    rotated_creatorWord_left_projection, smul_smul]
  have hi := DFunLike.congr_fun (secondQuantizationIsometry_adjoint_comp (doubledFirst H))
    (tensorAnnihilatorWord v f)
  change (doubledFockInclusion H).toContinuousLinearMap.adjoint
    (doubledFockInclusion H (tensorAnnihilatorWord v f)) = tensorAnnihilatorWord v f at hi
  rw [hi, pow_add, mul_comm]

/-- Literal sum of every normal-ordered cut for arbitrary one-particle vectors. -/
def tensorNormalOrder (w : List H) : TensorFullFock H →L[ℂ] TensorFullFock H :=
  ∑ k : Fin (w.length + 1), tensorCreatorWord (w.take k.val) * tensorAnnihilatorWord (w.drop k.val)

/-- Full actual normal-order scaling, simultaneously for all cuts of an arbitrary vector word. -/
theorem rotated_tensorNormalOrder_compression (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1) (w : List H) :
    secondQuantizationCompression (doubledFirst H) (tensorNormalOrder (rotatedFirstWord r s hrs w)) =
      (r : ℂ) ^ w.length • tensorNormalOrder w := by
  have hl : (rotatedFirstWord r s hrs w).length = w.length := List.length_map _
  unfold tensorNormalOrder
  rw [hl, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have htake : (rotatedFirstWord r s hrs w).take k.val = rotatedFirstWord r s hrs (w.take k.val) :=
    by simp [rotatedFirstWord]
  have hdrop : (rotatedFirstWord r s hrs w).drop k.val = rotatedFirstWord r s hrs (w.drop k.val) :=
    by simp [rotatedFirstWord]
  rw [htake, hdrop, rotated_normalOrder_cut_compression]
  congr 1
  have hk : (w.take k.val).length + (w.drop k.val).length = w.length := by
    simpa only [List.length_append] using congrArg List.length (List.take_append_drop k.val w)
  exact congrArg (fun n => (r : ℂ) ^ n) hk

end FreeProbability.Fock

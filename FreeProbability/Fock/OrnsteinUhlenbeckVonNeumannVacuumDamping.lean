import FreeProbability.Fock.OrnsteinUhlenbeckVonNeumannVacuumSandwich

/-! The actual rotation sandwich equals degree damping on the entire completed tensor Fock space. -/
noncomputable section
open scoped Classical InnerProductSpace ENNReal
namespace FreeProbability.Fock
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Basis words are transported to their actual creator-word vacuum vectors. -/
theorem ou_fullTensorWord_creatorVacuum (w : List (fullFockBasisSet H)) :
    fullFockTensorDecomposition H (word w) =
      tensorCreatorWord (w.map (fullFockBasis H)) (tensorVacuum H) := by
  induction w with
  | nil => exact fullFockTensorDecomposition_vacuum H
  | cons i w ih =>
    have hs : fullFockTensorDecomposition H (word (i :: w)) =
        tensorCreation H (fullFockBasis H i) (fullFockTensorDecomposition H (word w)) := by
      rw [tensorCreation_apply, LinearIsometryEquiv.symm_apply_apply]
      change fullFockTensorDecomposition H (word (i :: w)) =
        fullFockTensorDecomposition H (basisCreation (fullFockBasis H) (fullFockBasis H i) (word w))
      rw [basisCreation_basis, creation_word]
    rw [hs, ih]
    rfl

/-- The genuine Hilbert-space rotation-compression equals the actual degree operator on ALL vectors. -/
theorem ouVacuumSandwich_eq_degreeDamping (t : ℝ) (ht : 0 ≤ t) :
    ouVacuumSandwich (H := H) (ouCosine t) (ouSine t) (ouRotation_parameters t ht) =
      degreeDamping H t ht := by
  let U := fullFockTensorDecomposition H
  let A := ouVacuumSandwich (H := H) (ouCosine t) (ouSine t) (ouRotation_parameters t ht)
  let B := degreeDamping H t ht
  have hw : ∀ w : List (fullFockBasisSet H), A (U (word w)) = B (U (word w)) := by
    intro w
    change ouVacuumSandwich (ouCosine t) (ouSine t) (ouRotation_parameters t ht)
        (fullFockTensorDecomposition H (word w)) =
      degreeDamping H t ht (fullFockTensorDecomposition H (word w))
    rw [ou_fullTensorWord_creatorVacuum, ouVacuumSandwich_creatorWord]
    rw [tensorCreatorWord_vacuum_degree, degreeDamping_single]
    rfl
  have hcomp : A.comp U.toLinearIsometry.toContinuousLinearMap =
      B.comp U.toLinearIsometry.toContinuousLinearMap := by
    apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    intro w
    apply ContinuousLinearMap.ext
    intro c
    change A (U (lp.single 2 w c)) = B (U (lp.single 2 w c))
    have hs : (lp.single 2 w c : FullFock H) = c • word w := by
      apply lp.ext
      funext v
      simp [word, lp.single_apply, Pi.single_apply]
    rw [hs, map_smul, map_smul, map_smul]
    exact congrArg (c • ·) (hw w)
  apply ContinuousLinearMap.ext
  intro f
  have he := DFunLike.congr_fun hcomp (U.symm f)
  simpa only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.apply_symm_apply] using he

end FreeProbability.Fock

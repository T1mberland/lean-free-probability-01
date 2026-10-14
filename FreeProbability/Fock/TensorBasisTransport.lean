import FreeProbability.Fock.OrthonormalFamilyCalculus
import FreeProbability.Fock.TensorOperators

/-! # Genuine adapted-basis unitary onto the fixed completed tensor Fock space -/
noncomputable section
open scoped Classical InnerProductSpace TensorProduct
open UniformSpace
namespace FreeProbability.Fock.OrthonormalFamilyExtension
variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {e : I → H} (d : OrthonormalFamilyExtension e)

/-- Actual recursively completed tensor-level unitary, for every adapted Hilbert basis. -/
def tensorLevelTransport : ∀ n, WordLevel d.indices n ≃ₗᵢ[ℂ] TensorPower H n
  | 0 => d.scalarLevel.symm.trans (tensorPowerZero H)
  | n + 1 => (d.successorTensorEquiv n).symm.trans
      (isometryEquivCompletion (TensorProduct.congrIsometry (LinearIsometryEquiv.refl ℂ H)
        (tensorLevelTransport n)))

/-- The scalar sector agrees exactly with the fixed tensor scalar sector. -/
@[simp] theorem tensorLevelTransport_zero (c : ℂ) :
    d.tensorLevelTransport 0 (d.scalarLevel c) = tensorPowerZero H c := by
  simp [tensorLevelTransport]

/-- Completed successor transport respects literal tensoring by every original vector. -/
theorem tensorLevelTransport_successor (n : ℕ) (h : H) (f : WordLevel d.indices n) :
    d.tensorLevelTransport (n + 1) (d.successorTensorEquiv n
      ((h ⊗ₜ[ℂ] f : H ⊗[ℂ] WordLevel d.indices n) : Completion (H ⊗[ℂ] WordLevel d.indices n))) =
      ((h ⊗ₜ[ℂ] d.tensorLevelTransport n f : H ⊗[ℂ] TensorPower H n) :
        Completion (H ⊗[ℂ] TensorPower H n)) := by
  change isometryEquivCompletion _ ((d.successorTensorEquiv n).symm (d.successorTensorEquiv n _)) = _
  rw [LinearIsometryEquiv.symm_apply_apply, isometryEquivCompletion_coe]
  simp only [TensorProduct.congrIsometry_apply, TensorProduct.congr_tmul]
  rfl

/-- Genuine onto full-space unitary; the codomain is the fixed literal tensor Hilbert sum. -/
def tensorTransport : d.Space ≃ₗᵢ[ℂ] TensorFullFock H :=
  d.grading.trans (hilbertSumEquiv d.tensorLevelTransport)

/-- Each complete degree sector is transported to the corresponding fixed tensor power. -/
@[simp] theorem tensorTransport_level (n : ℕ) (f : WordLevel d.indices n) :
    d.tensorTransport (levelEmbedding n f) = lp.single 2 n (d.tensorLevelTransport n f) := by
  have hg : d.grading (levelEmbedding n f) = lp.single 2 n f := by
    have hl : d.grading.symm (lp.single 2 n f) = levelEmbedding n f :=
      lengthDecomposition_symm_single n f
    exact (congrArg d.grading hl).symm.trans (d.grading.apply_symm_apply _)
  change hilbertSumEquiv d.tensorLevelTransport (d.grading (levelEmbedding n f)) = _
  rw [hg, hilbertSumEquiv_single]

@[simp] theorem tensorTransport_vacuum : d.tensorTransport d.vacuum = tensorVacuum H := by
  change hilbertSumEquiv d.tensorLevelTransport (d.grading d.vacuum) = _
  rw [d.grading_vacuum, hilbertSumEquiv_single, d.tensorLevelTransport_zero]
  rfl

/-- True creation intertwining on the entire complete adapted Fock space. -/
theorem tensorTransport_creation (h : H) (f : d.Space) :
    d.tensorTransport (d.creation h f) = tensorCreation H h (d.tensorTransport f) := by
  let L := (d.tensorTransport.toLinearIsometry.toContinuousLinearMap.comp (d.creation h)).comp
    d.grading.symm.toLinearIsometry.toContinuousLinearMap
  let R := ((tensorCreation H h).comp d.tensorTransport.toLinearIsometry.toContinuousLinearMap).comp
    d.grading.symm.toLinearIsometry.toContinuousLinearMap
  have hLR : L = R := by
    apply lp.ext_continuousLinearMap (ENNReal.ofNat_ne_top (n := 2))
    intro n
    apply ContinuousLinearMap.ext
    intro g
    change d.tensorTransport (d.creation h (d.grading.symm (lp.single 2 n g))) =
      tensorCreation H h (d.tensorTransport (d.grading.symm (lp.single 2 n g)))
    have hg : d.grading.symm (lp.single 2 n g) = levelEmbedding n g :=
      lengthDecomposition_symm_single n g
    rw [hg]
    calc
      _ = d.tensorTransport (levelEmbedding (n + 1) (d.successorTensorEquiv n
          ((h ⊗ₜ[ℂ] g : H ⊗[ℂ] WordLevel d.indices n) :
            Completion (H ⊗[ℂ] WordLevel d.indices n)))) :=
        congrArg d.tensorTransport (d.tensor_creation n h g).symm
      _ = lp.single 2 (n + 1) (d.tensorLevelTransport (n + 1) (d.successorTensorEquiv n
          ((h ⊗ₜ[ℂ] g : H ⊗[ℂ] WordLevel d.indices n) :
            Completion (H ⊗[ℂ] WordLevel d.indices n)))) := d.tensorTransport_level _ _
      _ = tensorCreation H h (lp.single 2 n (d.tensorLevelTransport n g)) :=
        (congrArg (lp.single 2 (n + 1)) (d.tensorLevelTransport_successor n h g)).trans
          (tensorCreation_single H n h (d.tensorLevelTransport n g)).symm
      _ = _ := congrArg (tensorCreation H h) (d.tensorTransport_level n g).symm
  have hf := DFunLike.congr_fun hLR (d.grading f)
  change d.tensorTransport (d.creation h (d.grading.symm (d.grading f))) =
    tensorCreation H h (d.tensorTransport (d.grading.symm (d.grading f))) at hf
  rw [d.grading.symm_apply_apply] at hf
  exact hf

end FreeProbability.Fock.OrthonormalFamilyExtension

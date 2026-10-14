import FreeProbability.Fock.SecondQuantizationTensor

/-! # Second quantization intertwines actual creation and adjoint annihilation -/

noncomputable section
open scoped Classical InnerProductSpace TensorProduct

namespace FreeProbability.Fock

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Creation intertwining on the entire completed tensor Fock space. -/
theorem secondQuantization_creation_comp (U : H ≃ₗᵢ[ℂ] H) (h : H) :
    (secondQuantization U).toLinearIsometry.toContinuousLinearMap.comp (tensorCreation H h) =
      (tensorCreation H (U h)).comp (secondQuantization U).toLinearIsometry.toContinuousLinearMap := by
  apply lp.ext_continuousLinearMap (ENNReal.ofNat_ne_top (n := 2))
  intro n
  apply ContinuousLinearMap.ext
  intro f
  change secondQuantization U (tensorCreation H h (lp.single 2 n f)) =
    tensorCreation H (U h) (secondQuantization U (lp.single 2 n f))
  let x : TensorPower H (n + 1) := ((h ⊗ₜ[ℂ] f : H ⊗[ℂ] TensorPower H n) :
    UniformSpace.Completion (H ⊗[ℂ] TensorPower H n))
  calc
    secondQuantization U (tensorCreation H h (lp.single 2 n f)) =
        secondQuantization U (lp.single 2 (n + 1) x) :=
      congrArg (secondQuantization U) (tensorCreation_single H n h f)
    _ = lp.single 2 (n + 1) (tensorPowerUnitary U (n + 1) x) :=
      secondQuantization_single U (n + 1) x
    _ = tensorCreation H (U h) (lp.single 2 n (tensorPowerUnitary U n f)) := by
      exact (congrArg (lp.single 2 (n + 1)) (tensorPowerUnitary_tmul U n h f)).trans
        (tensorCreation_single H n (U h) (tensorPowerUnitary U n f)).symm
    _ = tensorCreation H (U h) (secondQuantization U (lp.single 2 n f)) :=
      congrArg (tensorCreation H (U h)) (secondQuantization_single U n f).symm


/-- Pointwise creation transport holds for arbitrary infinite tensor sums. -/
theorem secondQuantization_creation (U : H ≃ₗᵢ[ℂ] H) (h : H) (f : TensorFullFock H) :
    secondQuantization U (tensorCreation H h f) =
      tensorCreation H (U h) (secondQuantization U f) :=
  DFunLike.congr_fun (secondQuantization_creation_comp U h) f

/-- Unitary conjugation sends creation of h to creation of U h. -/
@[simp] theorem secondQuantization_conj_creation (U : H ≃ₗᵢ[ℂ] H) (h : H) :
    (secondQuantization U).conjStarAlgEquiv (tensorCreation H h) = tensorCreation H (U h) := by
  apply ContinuousLinearMap.ext
  intro f
  change secondQuantization U
    (tensorCreation H h ((secondQuantization U).symm f)) = _
  rw [secondQuantization_creation, LinearIsometryEquiv.apply_symm_apply]

/-- The adjoint is transported by the same actual unitary conjugation. -/
@[simp] theorem secondQuantization_conj_annihilation (U : H ≃ₗᵢ[ℂ] H) (h : H) :
    (secondQuantization U).conjStarAlgEquiv (tensorAnnihilation H h) =
      tensorAnnihilation H (U h) := by
  change (secondQuantization U).conjStarAlgEquiv (star (tensorCreation H h)) =
    star (tensorCreation H (U h))
  rw [map_star, secondQuantization_conj_creation]

/-- Equivalent genuine second quantization in the complete word realization of F(H). -/
def fullSecondQuantization (U : H ≃ₗᵢ[ℂ] H) : FullFock H ≃ₗᵢ[ℂ] FullFock H :=
  ((fullFockTensorDecomposition H).trans (secondQuantization U)).trans
    (fullFockTensorDecomposition H).symm

@[simp] theorem fullSecondQuantization_vacuum (U : H ≃ₗᵢ[ℂ] H) :
    fullSecondQuantization U (fullVacuum H) = fullVacuum H := by
  change (fullFockTensorDecomposition H).symm
    (secondQuantization U (fullFockTensorDecomposition H (fullVacuum H))) = _
  rw [fullFockTensorDecomposition_vacuum]
  change (fullFockTensorDecomposition H).symm (secondQuantization U (tensorVacuum H)) = _
  rw [secondQuantization_vacuum]
  exact (fullFockTensorDecomposition H).injective (by simp [tensorVacuum])

/-- Creation transport in the complete original-H realization. -/
theorem fullSecondQuantization_creation (U : H ≃ₗᵢ[ℂ] H) (h : H) (f : FullFock H) :
    fullSecondQuantization U (fullCreation H h f) =
      fullCreation H (U h) (fullSecondQuantization U f) := by
  apply (fullFockTensorDecomposition H).injective
  change fullFockTensorDecomposition H
    ((fullFockTensorDecomposition H).symm
      (secondQuantization U (fullFockTensorDecomposition H (fullCreation H h f)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  have hc := secondQuantization_creation U h (fullFockTensorDecomposition H f)
  simpa only [tensorCreation_apply, LinearIsometryEquiv.symm_apply_apply,
    fullSecondQuantization, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply] using hc

end FreeProbability.Fock

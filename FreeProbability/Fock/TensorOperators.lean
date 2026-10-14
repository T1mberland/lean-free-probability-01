import FreeProbability.Fock.TensorPower

/-!
# Bounded operators on the explicit completed-tensor full Fock space

The full Fock unitary transports actual bounded creation and its Hilbert adjoint
onto the Hilbert sum of the explicitly recursive completed tensor powers.
-/

noncomputable section
open scoped Classical InnerProductSpace TensorProduct
open UniformSpace

namespace FreeProbability.Fock

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Unitary transport of bounded operators onto the genuine tensor-sum domain. -/
def tensorOperatorEquiv : (FullFock H →L[ℂ] FullFock H) ≃⋆ₐ[ℂ]
    (TensorFullFock H →L[ℂ] TensorFullFock H) := (fullFockTensorDecomposition H).conjStarAlgEquiv

/-- Actual bounded creation on the explicitly recursively completed full Fock space. -/
def tensorCreation (h : H) : TensorFullFock H →L[ℂ] TensorFullFock H :=
  tensorOperatorEquiv H (fullCreation H h)

/-- Actual adjoint annihilation on the explicitly recursively completed full Fock space. -/
def tensorAnnihilation (h : H) : TensorFullFock H →L[ℂ] TensorFullFock H := (tensorCreation H h).adjoint

/-- The genuine tensor-sum vacuum, supported exactly in degree zero. -/
def tensorVacuum : TensorFullFock H := lp.single 2 0 (tensorPowerZero H 1)

@[simp] theorem norm_tensorVacuum : ‖tensorVacuum H‖ = 1 := by
  change ‖lp.single 2 0 (tensorPowerZero H 1)‖ = 1
  rw [← fullFockTensorDecomposition_vacuum]
  simp

@[simp] theorem tensorCreation_apply (h : H) (f : TensorFullFock H) :
    tensorCreation H h f = fullFockTensorDecomposition H
      (fullCreation H h ((fullFockTensorDecomposition H).symm f)) := rfl

/-- Exact norm on every vector, not only elementary tensors. -/
@[simp] theorem norm_tensorCreation_apply (h : H) (f : TensorFullFock H) :
    ‖tensorCreation H h f‖ = ‖h‖ * ‖f‖ := by
  rw [tensorCreation_apply, LinearIsometryEquiv.norm_map]
  change ‖vectorCreation ((fullFockBasis H).repr h)
    ((fullFockTensorDecomposition H).symm f)‖ = _
  rw [norm_vectorCreation_apply, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]

@[simp] theorem norm_tensorCreation (h : H) : ‖tensorCreation H h‖ = ‖h‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg h)
    intro f
    exact (norm_tensorCreation_apply H h f).le
  · have he := (tensorCreation H h).le_opNorm (tensorVacuum H)
    rw [norm_tensorCreation_apply, norm_tensorVacuum, mul_one] at he
    simpa only [mul_one] using he

@[simp] theorem norm_tensorAnnihilation (h : H) : ‖tensorAnnihilation H h‖ = ‖h‖ := by
  rw [tensorAnnihilation, ContinuousLinearMap.adjoint.norm_map, norm_tensorCreation]

/-- Adjoint transport uses the actual star-algebra unitary, not a separately assumed relation. -/
theorem tensorAnnihilation_eq_transport (h : H) :
    tensorAnnihilation H h = tensorOperatorEquiv H (fullAnnihilation H h) := by
  change star (tensorOperatorEquiv H (fullCreation H h)) = tensorOperatorEquiv H (star (fullCreation H h))
  exact (map_star _ _).symm

/-- Canonical relation on the actual completed-tensor domain. -/
theorem tensorAnnihilation_creation (h k : H) :
    tensorAnnihilation H h * tensorCreation H k =
      inner ℂ h k • (1 : TensorFullFock H →L[ℂ] TensorFullFock H) := by
  rw [tensorAnnihilation_eq_transport, tensorCreation, ← map_mul,
    fullAnnihilation_creation, map_smul, map_one]

@[simp] theorem tensorAnnihilation_vacuum (h : H) :
    tensorAnnihilation H h (tensorVacuum H) = 0 := by
  rw [tensorAnnihilation_eq_transport]
  change (fullFockTensorDecomposition H)
    (fullAnnihilation H h ((fullFockTensorDecomposition H).symm (tensorVacuum H))) = 0
  change (fullFockTensorDecomposition H)
    (fullAnnihilation H h ((fullFockTensorDecomposition H).symm (lp.single 2 0 (tensorPowerZero H 1)))) = 0
  simp

/-- On pure degree-n tensors creation is exactly tensoring into degree n+1. -/
theorem tensorCreation_single (n : ℕ) (h : H) (f : TensorPower H n) :
    tensorCreation H h (lp.single 2 n f) = lp.single 2 (n + 1)
      ((h ⊗ₜ[ℂ] f : H ⊗[ℂ] TensorPower H n) : Completion (H ⊗[ℂ] TensorPower H n)) := by
  apply (fullFockTensorDecomposition H).symm.injective
  rw [tensorCreation_apply, LinearIsometryEquiv.symm_apply_apply,
    fullFockTensorDecomposition_symm_single]
  let x : TensorPower H (n + 1) := ((h ⊗ₜ[ℂ] f : H ⊗[ℂ] TensorPower H n) :
    Completion (H ⊗[ℂ] TensorPower H n))
  exact (tensorPowerEmbedding_creation H n h f).symm.trans
    (fullFockTensorDecomposition_symm_single H (n + 1) x).symm

end FreeProbability.Fock

import FreeProbability.Fock.TensorOperators

/-!
# Second quantization on the genuine completed tensor Fock space

Each level is the recursively completed Hilbert tensor power. A one-particle
unitary acts on every tensor factor, fixes the scalar sector, and induces an
actual unitary on the entire Hilbert direct sum. This construction does not
assert preservation of a chosen real semicircular algebra.
-/

noncomputable section
open scoped Classical InnerProductSpace TensorProduct
open UniformSpace

namespace FreeProbability.Fock

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The tensor-power lift of a one-particle Hilbert unitary, on completed levels. -/
def tensorPowerUnitary (U : H ≃ₗᵢ[ℂ] H) : ∀ n, TensorPower H n ≃ₗᵢ[ℂ] TensorPower H n
  | 0 => LinearIsometryEquiv.refl ℂ _
  | n + 1 => isometryEquivCompletion
      (TensorProduct.congrIsometry U (tensorPowerUnitary U n))

@[simp] theorem tensorPowerUnitary_zero (U : H ≃ₗᵢ[ℂ] H) (f : TensorPower H 0) :
    tensorPowerUnitary U 0 f = f := rfl

/-- On elementary tensors the completed successor lift acts on both factors. -/
@[simp] theorem tensorPowerUnitary_tmul (U : H ≃ₗᵢ[ℂ] H) (n : ℕ)
    (h : H) (f : TensorPower H n) :
    tensorPowerUnitary U (n + 1)
      ((h ⊗ₜ[ℂ] f : H ⊗[ℂ] TensorPower H n) : Completion (H ⊗[ℂ] TensorPower H n)) =
      ((U h ⊗ₜ[ℂ] tensorPowerUnitary U n f : H ⊗[ℂ] TensorPower H n) :
        Completion (H ⊗[ℂ] TensorPower H n)) := by
  change isometryEquivCompletion _ _ = _
  rw [isometryEquivCompletion_coe]
  simp only [TensorProduct.congrIsometry_apply, TensorProduct.congr_tmul]
  rfl

/-- Genuine second quantization on the infinite sum of completed tensor powers. -/
def secondQuantization (U : H ≃ₗᵢ[ℂ] H) : TensorFullFock H ≃ₗᵢ[ℂ] TensorFullFock H :=
  hilbertSumEquiv (tensorPowerUnitary U)

/-- Every tensor grading coordinate is transported by its tensor-power unitary. -/
@[simp] theorem secondQuantization_apply_degree (U : H ≃ₗᵢ[ℂ] H)
    (f : TensorFullFock H) (n : ℕ) :
    secondQuantization U f n = tensorPowerUnitary U n (f n) := rfl

/-- Pure degree-n vectors remain in exactly degree n. -/
@[simp] theorem secondQuantization_single (U : H ≃ₗᵢ[ℂ] H) (n : ℕ)
    (f : TensorPower H n) :
    secondQuantization U (lp.single 2 n f) = lp.single 2 n (tensorPowerUnitary U n f) :=
  hilbertSumEquiv_single _ _ _

/-- The scalar vacuum is fixed by every second-quantized Hilbert unitary. -/
@[simp] theorem secondQuantization_vacuum (U : H ≃ₗᵢ[ℂ] H) :
    secondQuantization U (tensorVacuum H) = tensorVacuum H := by
  simp [tensorVacuum]

/-- Second quantization preserves the norm on all vectors, including infinite sums. -/
@[simp] theorem norm_secondQuantization (U : H ≃ₗᵢ[ℂ] H) (f : TensorFullFock H) :
    ‖secondQuantization U f‖ = ‖f‖ := (secondQuantization U).norm_map f

end FreeProbability.Fock

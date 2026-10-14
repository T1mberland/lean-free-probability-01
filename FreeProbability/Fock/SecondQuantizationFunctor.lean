import FreeProbability.Fock.SecondQuantizationOperators

/-! # Functoriality of completed tensor second quantization -/

noncomputable section
open scoped Classical InnerProductSpace TensorProduct
open UniformSpace

namespace FreeProbability.Fock
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Composition acts on every factor of each completed tensor power. -/
theorem tensorPowerUnitary_trans (U V : H ≃ₗᵢ[ℂ] H) (n : ℕ) (f : TensorPower H n) :
    tensorPowerUnitary (U.trans V) n f =
      tensorPowerUnitary V n (tensorPowerUnitary U n f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change isometryEquivCompletion _ f =
      isometryEquivCompletion _ (isometryEquivCompletion _ f)
    refine Completion.ext' (isometryEquivCompletion _).continuous
      ((isometryEquivCompletion _).continuous.comp (isometryEquivCompletion _).continuous) ?_ f
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul h g =>
      simp only [Function.comp_apply, isometryEquivCompletion_coe,
        TensorProduct.congrIsometry_apply, TensorProduct.congr_tmul]
      change ((V (U h) ⊗ₜ[ℂ] tensorPowerUnitary (U.trans V) n g :
        H ⊗[ℂ] TensorPower H n) : Completion (H ⊗[ℂ] TensorPower H n)) =
        ((V (U h) ⊗ₜ[ℂ] tensorPowerUnitary V n (tensorPowerUnitary U n g) :
        H ⊗[ℂ] TensorPower H n) : Completion (H ⊗[ℂ] TensorPower H n))
      rw [ih]
    | add x y hx hy =>
      simpa only [Function.comp_apply, Completion.coe_add, map_add] using congrArg₂ (· + ·) hx hy

/-- The identity one-particle map induces the identity on each completed level. -/
@[simp] theorem tensorPowerUnitary_refl (n : ℕ) (f : TensorPower H n) :
    tensorPowerUnitary (LinearIsometryEquiv.refl ℂ H) n f = f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change isometryEquivCompletion _ f = f
    refine Completion.ext' (isometryEquivCompletion _).continuous continuous_id ?_ f
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul h g =>
      simp only [isometryEquivCompletion_coe, TensorProduct.congrIsometry_apply,
        TensorProduct.congr_tmul]
      change ((h ⊗ₜ[ℂ] tensorPowerUnitary (LinearIsometryEquiv.refl ℂ H) n g :
        H ⊗[ℂ] TensorPower H n) : Completion (H ⊗[ℂ] TensorPower H n)) = _
      rw [ih]
      rfl
    | add x y hx hy => simpa only [id_eq, Completion.coe_add, map_add] using congrArg₂ (· + ·) hx hy

/-- Genuine second quantization respects composition, including infinite tensor sums. -/
theorem secondQuantization_trans (U V : H ≃ₗᵢ[ℂ] H) :
    secondQuantization (U.trans V) = (secondQuantization U).trans (secondQuantization V) := by
  apply LinearIsometryEquiv.ext
  intro f
  apply lp.ext
  funext n
  exact tensorPowerUnitary_trans U V n (f n)

@[simp] theorem secondQuantization_refl :
    secondQuantization (LinearIsometryEquiv.refl ℂ H) = LinearIsometryEquiv.refl ℂ (TensorFullFock H) := by
  apply LinearIsometryEquiv.ext
  intro f
  apply lp.ext
  funext n
  exact tensorPowerUnitary_refl n (f n)

/-- Inverse one-particle unitaries lift to inverse full-space unitaries. -/
@[simp] theorem secondQuantization_symm (U : H ≃ₗᵢ[ℂ] H) :
    secondQuantization U.symm = (secondQuantization U).symm := by
  apply LinearIsometryEquiv.ext
  intro f
  apply (secondQuantization U).injective
  have ht := secondQuantization_trans U.symm U
  have hf := DFunLike.congr_fun ht f
  simp only [LinearIsometryEquiv.symm_trans_self, secondQuantization_refl,
    LinearIsometryEquiv.trans_apply] at hf
  exact hf.symm.trans ((secondQuantization U).apply_symm_apply f).symm

/-- Vacuum expectation is invariant under actual bounded-operator conjugation. -/
theorem secondQuantization_vacuum_expectation (U : H ≃ₗᵢ[ℂ] H)
    (T : TensorFullFock H →L[ℂ] TensorFullFock H) :
    inner ℂ (tensorVacuum H) ((secondQuantization U).conjStarAlgEquiv T (tensorVacuum H)) =
      inner ℂ (tensorVacuum H) (T (tensorVacuum H)) := by
  have hs : (secondQuantization U).symm (tensorVacuum H) = tensorVacuum H := by
    apply (secondQuantization U).injective
    simp
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, hs]
  calc
    inner ℂ (tensorVacuum H) (secondQuantization U (T (tensorVacuum H))) =
      inner ℂ (secondQuantization U (tensorVacuum H))
        (secondQuantization U (T (tensorVacuum H))) := by rw [secondQuantization_vacuum]
    _ = _ := (secondQuantization U).inner_map_map _ _

end FreeProbability.Fock

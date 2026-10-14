import FreeProbability.Fock.SecondQuantizationFields

/-! # Genuine second quantization of arbitrary Hilbert-space isometries -/
noncomputable section
open scoped Classical InnerProductSpace TensorProduct ENNReal
open UniformSpace

namespace FreeProbability.Fock

section Completion
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Extend an isometry to the genuine completions, without a surjectivity assumption. -/
def linearIsometryCompletion (V : E →ₗᵢ[ℂ] F) : Completion E →ₗᵢ[ℂ] Completion F where
  toLinearMap := V.toContinuousLinearMap.completion.toLinearMap
  norm_map' x := by
    induction x using Completion.induction_on with
    | hp =>
      exact isClosed_eq
        (continuous_norm.comp V.toContinuousLinearMap.completion.continuous) continuous_norm
    | ih x => simp

@[simp] theorem linearIsometryCompletion_coe (V : E →ₗᵢ[ℂ] F) (x : E) :
    linearIsometryCompletion V (x : Completion E) = (V x : Completion F) :=
  ContinuousLinearMap.completion_apply_coe _ _
end Completion

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Isometric tensor-power transport on literal recursively completed tensor powers. -/
def tensorPowerIsometry (V : H →ₗᵢ[ℂ] K) : ∀ n, TensorPower H n →ₗᵢ[ℂ] TensorPower K n
  | 0 => ((tensorPowerZero H).symm.trans (tensorPowerZero K)).toLinearIsometry
  | n + 1 => linearIsometryCompletion (TensorProduct.mapIsometry V (tensorPowerIsometry V n))

@[simp] theorem tensorPowerIsometry_zero (V : H →ₗᵢ[ℂ] K) (c : ℂ) :
    tensorPowerIsometry V 0 (tensorPowerZero H c) = tensorPowerZero K c := by
  simp [tensorPowerIsometry]

@[simp] theorem tensorPowerIsometry_tmul (V : H →ₗᵢ[ℂ] K) (n : ℕ) (h : H)
    (f : TensorPower H n) :
    tensorPowerIsometry V (n + 1)
      ((h ⊗ₜ[ℂ] f : H ⊗[ℂ] TensorPower H n) : Completion (H ⊗[ℂ] TensorPower H n)) =
      ((V h ⊗ₜ[ℂ] tensorPowerIsometry V n f : K ⊗[ℂ] TensorPower K n) :
        Completion (K ⊗[ℂ] TensorPower K n)) := by
  change linearIsometryCompletion _ _ = _
  rw [linearIsometryCompletion_coe]
  rfl

/-- Second quantization is an actual isometry of the entire infinite Hilbert sum. -/
def secondQuantizationIsometry (V : H →ₗᵢ[ℂ] K) : TensorFullFock H →ₗᵢ[ℂ] TensorFullFock K where
  toFun f := ⟨fun n => tensorPowerIsometry V n (f n), by
    apply Memℓp.of_norm
    simpa only [(tensorPowerIsometry V _).norm_map] using (lp.memℓp f).norm⟩
  map_add' f g := by ext n; simp; rfl
  map_smul' c f := by ext n; simp
  norm_map' f := by
    rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal),
      lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    congr 1
    congr 1
    funext n
    exact congrArg (fun r : ℝ => r ^ (2 : ℝ≥0∞).toReal) ((tensorPowerIsometry V n).norm_map (f n))

@[simp] theorem secondQuantizationIsometry_degree (V : H →ₗᵢ[ℂ] K)
    (f : TensorFullFock H) (n : ℕ) :
    secondQuantizationIsometry V f n = tensorPowerIsometry V n (f n) := rfl

@[simp] theorem secondQuantizationIsometry_single (V : H →ₗᵢ[ℂ] K) (n : ℕ)
    (f : TensorPower H n) :
    secondQuantizationIsometry V (lp.single 2 n f) = lp.single 2 n (tensorPowerIsometry V n f) := by
  ext j
  by_cases hj : j = n
  · subst j; simp [lp.single_apply]
  · simp [lp.single_apply, hj]

@[simp] theorem secondQuantizationIsometry_vacuum (V : H →ₗᵢ[ℂ] K) :
    secondQuantizationIsometry V (tensorVacuum H) = tensorVacuum K := by
  simp [tensorVacuum]

/-- Actual creation intertwining, including all infinite tensor sums. -/
theorem secondQuantizationIsometry_creation_comp (V : H →ₗᵢ[ℂ] K) (h : H) :
    (secondQuantizationIsometry V).toContinuousLinearMap.comp (tensorCreation H h) =
      (tensorCreation K (V h)).comp (secondQuantizationIsometry V).toContinuousLinearMap := by
  apply lp.ext_continuousLinearMap (ENNReal.ofNat_ne_top (n := 2))
  intro n
  apply ContinuousLinearMap.ext
  intro f
  change secondQuantizationIsometry V (tensorCreation H h (lp.single 2 n f)) =
    tensorCreation K (V h) (secondQuantizationIsometry V (lp.single 2 n f))
  let x : TensorPower H (n + 1) := ((h ⊗ₜ[ℂ] f : H ⊗[ℂ] TensorPower H n) :
    Completion (H ⊗[ℂ] TensorPower H n))
  calc
    _ = secondQuantizationIsometry V (lp.single 2 (n + 1) x) :=
      congrArg (secondQuantizationIsometry V) (tensorCreation_single H n h f)
    _ = lp.single 2 (n + 1) (tensorPowerIsometry V (n + 1) x) :=
      secondQuantizationIsometry_single V (n + 1) x
    _ = tensorCreation K (V h) (lp.single 2 n (tensorPowerIsometry V n f)) :=
      (congrArg (lp.single 2 (n + 1)) (tensorPowerIsometry_tmul V n h f)).trans
        (tensorCreation_single K n (V h) (tensorPowerIsometry V n f)).symm
    _ = _ := congrArg (tensorCreation K (V h)) (secondQuantizationIsometry_single V n f).symm

end FreeProbability.Fock

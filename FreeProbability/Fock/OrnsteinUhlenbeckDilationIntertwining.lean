import FreeProbability.Fock.OrnsteinUhlenbeckDilationGenerators

/-! # Strong annihilation and creator projection identities for actual Fock inclusion -/
noncomputable section
open scoped Classical InnerProductSpace TensorProduct
open UniformSpace
namespace FreeProbability.Fock

theorem ou_scalar_single (L : Type*) [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L] (c : ℂ) :
    lp.single 2 0 (tensorPowerZero L c) = c • tensorVacuum L := by
  calc
    _ = lp.single 2 0 (tensorPowerZero L (c • (1 : ℂ))) := by simp
    _ = _ := by
      rw [map_smul]
      exact map_smul (lp.singleContinuousLinearMap ℂ (fun n => TensorPower L n) 2 0) c _

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Included annihilation intertwines in the direction needed for normal-order compression.
This is a stronger assertion than the adjoint of creation intertwining. -/
theorem inclusion_annihilation_comp (V : H →ₗᵢ[ℂ] K) (h : H) :
    (tensorAnnihilation K (V h)).comp (secondQuantizationIsometry V).toContinuousLinearMap =
      (secondQuantizationIsometry V).toContinuousLinearMap.comp (tensorAnnihilation H h) := by
  apply lp.ext_continuousLinearMap (ENNReal.ofNat_ne_top (n := 2))
  intro n
  apply ContinuousLinearMap.ext
  intro f
  change tensorAnnihilation K (V h) (secondQuantizationIsometry V (lp.single 2 n f)) =
    secondQuantizationIsometry V (tensorAnnihilation H h (lp.single 2 n f))
  cases n with
  | zero =>
    obtain ⟨c, rfl⟩ := (tensorPowerZero H).surjective f
    rw [secondQuantizationIsometry_single, tensorPowerIsometry_zero, ou_scalar_single K c, ou_scalar_single H c]
    simp only [map_smul, tensorAnnihilation_vacuum, smul_zero, map_zero]
  | succ n =>
    induction f using Completion.induction_on with
    | hp =>
      exact isClosed_eq
        ((tensorAnnihilation K (V h)).continuous.comp
          ((secondQuantizationIsometry V).continuous.comp
            (lp.singleContinuousLinearMap ℂ (fun m => TensorPower H m) 2 (n + 1)).continuous))
        ((secondQuantizationIsometry V).continuous.comp
          ((tensorAnnihilation H h).continuous.comp
            (lp.singleContinuousLinearMap ℂ (fun m => TensorPower H m) 2 (n + 1)).continuous))
    | ih x =>
      induction x using TensorProduct.inductionOn with
      | tmul a g =>
        let x' : TensorPower H (n + 1) := ((a ⊗ₜ[ℂ] g : H ⊗[ℂ] TensorPower H n) :
          Completion (H ⊗[ℂ] TensorPower H n))
        let y' : TensorPower K (n + 1) := ((V a ⊗ₜ[ℂ] tensorPowerIsometry V n g :
          K ⊗[ℂ] TensorPower K n) : Completion (K ⊗[ℂ] TensorPower K n))
        calc
          _ = tensorAnnihilation K (V h) (lp.single 2 (n + 1) (tensorPowerIsometry V (n + 1) x')) :=
            congrArg (tensorAnnihilation K (V h)) (secondQuantizationIsometry_single V _ x')
          _ = tensorAnnihilation K (V h) (lp.single 2 (n + 1) y') :=
            congrArg (fun z : TensorPower K (n + 1) =>
              tensorAnnihilation K (V h) (lp.single 2 (n + 1) z)) (tensorPowerIsometry_tmul V n a g)
          _ = inner ℂ h a • lp.single 2 n (tensorPowerIsometry V n g) := by
            have ha := tensorAnnihilation_single_tmul (V h) (V a) n (tensorPowerIsometry V n g)
            rw [V.inner_map_map] at ha
            exact ha
          _ = secondQuantizationIsometry V (inner ℂ h a • lp.single 2 n g) :=
            (map_smul (secondQuantizationIsometry V) _ _).trans
              (congrArg (inner ℂ h a • ·) (secondQuantizationIsometry_single V n g)) |>.symm
          _ = _ := congrArg (secondQuantizationIsometry V) (tensorAnnihilation_single_tmul h a n g).symm
      | add x y hx hy =>
        let x' : TensorPower H (n + 1) := (x : Completion (H ⊗[ℂ] TensorPower H n))
        let y' : TensorPower H (n + 1) := (y : Completion (H ⊗[ℂ] TensorPower H n))
        have hs : lp.single (E := fun m => TensorPower H m) 2 (n + 1) (x' + y') =
            lp.single 2 (n + 1) x' + lp.single 2 (n + 1) y' :=
          map_add (lp.singleContinuousLinearMap ℂ (fun m => TensorPower H m) 2 (n + 1)) x' y'
        rw [Completion.coe_add]
        change tensorAnnihilation K (V h) (secondQuantizationIsometry V
          (lp.single 2 (n + 1) (x' + y'))) =
            secondQuantizationIsometry V (tensorAnnihilation H h (lp.single 2 (n + 1) (x' + y')))
        rw [hs, map_add, map_add, map_add, map_add]
        exact congrArg₂ (· + ·) hx hy

/-- Left projection of included creation, with actual adjoint on the full target Fock space. -/
theorem inclusion_adjoint_creation_comp (V : H →ₗᵢ[ℂ] K) (h : H) :
    (secondQuantizationIsometry V).toContinuousLinearMap.adjoint.comp (tensorCreation K (V h)) =
      (tensorCreation H h).comp (secondQuantizationIsometry V).toContinuousLinearMap.adjoint := by
  have ha := congrArg ContinuousLinearMap.adjoint (inclusion_annihilation_comp V h)
  simpa only [ContinuousLinearMap.adjoint_comp, tensorAnnihilation,
    ContinuousLinearMap.adjoint_adjoint] using ha

end FreeProbability.Fock

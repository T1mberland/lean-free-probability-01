import FreeProbability.Fock.OrnsteinUhlenbeckRotationTime

/-! # Genuine orthogonal-noise projection in the Fock inclusion -/
noncomputable section
open scoped Classical InnerProductSpace TensorProduct
open UniformSpace

namespace FreeProbability.Fock
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Annihilation of an elementary successor tensor is the exact inner-product contraction. -/
theorem tensorAnnihilation_single_tmul (k h : K) (n : ℕ) (f : TensorPower K n) :
    tensorAnnihilation K k (lp.single 2 (n + 1)
      (((h ⊗ₜ[ℂ] f : K ⊗[ℂ] TensorPower K n) : Completion (K ⊗[ℂ] TensorPower K n)) :
        TensorPower K (n + 1))) = inner ℂ k h • lp.single 2 n f := by
  have hc := DFunLike.congr_fun (tensorAnnihilation_creation K k h) (lp.single 2 n f)
  change tensorAnnihilation K k (tensorCreation K h (lp.single 2 n f)) =
    inner ℂ k h • lp.single 2 n f at hc
  exact (congrArg (tensorAnnihilation K k) (tensorCreation_single K n h f)).symm.trans hc

/-- Genuine orthogonal annihilation vanishes on the whole included complete Fock space. -/
theorem orthogonal_tensorAnnihilation_inclusion (V : H →ₗᵢ[ℂ] K) (k : K)
    (hk : ∀ h : H, inner ℂ k (V h) = 0) :
    (tensorAnnihilation K k).comp (secondQuantizationIsometry V).toContinuousLinearMap = 0 := by
  apply lp.ext_continuousLinearMap (ENNReal.ofNat_ne_top (n := 2))
  intro n
  apply ContinuousLinearMap.ext
  intro f
  change tensorAnnihilation K k (secondQuantizationIsometry V (lp.single 2 n f)) = 0
  cases n with
  | zero =>
    obtain ⟨c, rfl⟩ := (tensorPowerZero H).surjective f
    rw [secondQuantizationIsometry_single, tensorPowerIsometry_zero]
    have hs : lp.single 2 0 (tensorPowerZero K c) = c • tensorVacuum K := by
      calc
        _ = lp.single 2 0 (tensorPowerZero K (c • (1 : ℂ))) := by simp
        _ = c • lp.single 2 0 (tensorPowerZero K 1) := by
          rw [map_smul]
          exact map_smul (lp.singleContinuousLinearMap ℂ (fun n => TensorPower K n) 2 0) c _
    rw [hs, map_smul, tensorAnnihilation_vacuum, smul_zero]
  | succ n =>
    induction f using Completion.induction_on with
    | hp =>
      exact isClosed_eq
        ((tensorAnnihilation K k).continuous.comp
          ((secondQuantizationIsometry V).continuous.comp
            (lp.singleContinuousLinearMap ℂ (fun m => TensorPower H m) 2 (n + 1)).continuous))
        continuous_const
    | ih x =>
      induction x using TensorProduct.inductionOn with
      | tmul h g =>
        have he := secondQuantizationIsometry_single V (n + 1)
          (((h ⊗ₜ[ℂ] g : H ⊗[ℂ] TensorPower H n) : Completion (H ⊗[ℂ] TensorPower H n)) :
            TensorPower H (n + 1))
        have ht := tensorPowerIsometry_tmul V n h g
        have ha := tensorAnnihilation_single_tmul k (V h) n (tensorPowerIsometry V n g)
        rw [hk, zero_smul] at ha
        exact (congrArg (tensorAnnihilation K k) he).trans
          ((congrArg (fun z : TensorPower K (n + 1) =>
            tensorAnnihilation K k (lp.single 2 (n + 1) z)) ht).trans ha)
      | add x y hx hy =>
        let x' : TensorPower H (n + 1) := (x : Completion (H ⊗[ℂ] TensorPower H n))
        let y' : TensorPower H (n + 1) := (y : Completion (H ⊗[ℂ] TensorPower H n))
        have hs : lp.single (E := fun m => TensorPower H m) 2 (n + 1) (x' + y') =
            lp.single 2 (n + 1) x' + lp.single 2 (n + 1) y' :=
          map_add (lp.singleContinuousLinearMap ℂ (fun m => TensorPower H m) 2 (n + 1)) x' y'
        rw [Completion.coe_add]
        change tensorAnnihilation K k (secondQuantizationIsometry V
          (lp.single 2 (n + 1) (x' + y'))) = 0
        rw [hs, map_add, map_add]
        exact (congrArg₂ (· + ·) hx hy).trans (zero_add _)


omit [CompleteSpace H] in
/-- The doubled noise component is orthogonal to every included one-particle vector. -/
theorem doubled_noise_orthogonal (k h : H) :
    inner ℂ (doubledSecond H k) (doubledFirst H h) = 0 := by
  simp [doubledFirst, doubledSecond, WithLp.prod_inner_apply]

/-- Actual noise annihilation kills the included full Fock space. -/
theorem doubled_noise_annihilation_inclusion (k : H) :
    (tensorAnnihilation (DoubledHilbert H) (doubledSecond H k)).comp
      (doubledFockInclusion H).toContinuousLinearMap = 0 :=
  orthogonal_tensorAnnihilation_inclusion (doubledFirst H) (doubledSecond H k)
    (doubled_noise_orthogonal k)

/-- Included creation compresses to the actual original creation operator. -/
theorem inclusion_compression_creation (V : H →ₗᵢ[ℂ] K) (h : H) :
    secondQuantizationCompression V (tensorCreation K (V h)) = tensorCreation H h := by
  apply ContinuousLinearMap.ext
  intro f
  change (secondQuantizationIsometry V).toContinuousLinearMap.adjoint
    (tensorCreation K (V h) (secondQuantizationIsometry V f)) = _
  have hc := DFunLike.congr_fun (secondQuantizationIsometry_creation_comp V h) f
  change secondQuantizationIsometry V (tensorCreation H h f) =
    tensorCreation K (V h) (secondQuantizationIsometry V f) at hc
  rw [← hc]
  exact DFunLike.congr_fun (secondQuantizationIsometry_adjoint_comp V) (tensorCreation H h f)

/-- Orthogonal noise creation has zero actual compression. -/
theorem orthogonal_compression_creation (V : H →ₗᵢ[ℂ] K) (k : K)
    (hk : ∀ h : H, inner ℂ k (V h) = 0) :
    secondQuantizationCompression V (tensorCreation K k) = 0 := by
  have ha := congrArg ContinuousLinearMap.adjoint (orthogonal_tensorAnnihilation_inclusion V k hk)
  simp only [ContinuousLinearMap.adjoint_comp, tensorAnnihilation,
    ContinuousLinearMap.adjoint_adjoint, map_zero] at ha
  apply ContinuousLinearMap.ext
  intro f
  change (secondQuantizationIsometry V).toContinuousLinearMap.adjoint
    (tensorCreation K k (secondQuantizationIsometry V f)) = 0
  exact DFunLike.congr_fun ha (secondQuantizationIsometry V f)

/-- Orthogonal noise annihilation has zero actual compression. -/
theorem orthogonal_compression_annihilation (V : H →ₗᵢ[ℂ] K) (k : K)
    (hk : ∀ h : H, inner ℂ k (V h) = 0) :
    secondQuantizationCompression V (tensorAnnihilation K k) = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  change (secondQuantizationIsometry V).toContinuousLinearMap.adjoint
    (tensorAnnihilation K k (secondQuantizationIsometry V f)) = 0
  have ha := DFunLike.congr_fun (orthogonal_tensorAnnihilation_inclusion V k hk) f
  change tensorAnnihilation K k (secondQuantizationIsometry V f) = 0 at ha
  rw [ha, map_zero]

end FreeProbability.Fock

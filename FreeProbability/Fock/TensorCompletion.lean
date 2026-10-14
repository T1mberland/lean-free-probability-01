import FreeProbability.Fock.LengthDecomposition
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Completion

/-!
# Genuine completed Hilbert tensors with a square-summable first factor

The Hilbert completion of `ℓ²(I, ℂ) ⊗[ℂ] E` is isometrically equivalent to
`ℓ²(I, E)`. The algebraic tensor product is never assumed complete.
-/

noncomputable section
open scoped Classical InnerProductSpace TensorProduct ENNReal
open UniformSpace

namespace FreeProbability.Fock

variable {I E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Elementary tensors as genuinely square-summable families. -/
def hilbertTensorFamily (h : OneParticleSpace I) (f : E) : lp (fun _ : I => E) 2 :=
  ⟨fun i => h i • f, by
    apply Memℓp.of_norm
    convert (lp.memℓp h).norm.const_smul ‖f‖ using 1
    ext i
    simp [norm_smul, mul_comm]⟩

@[simp] theorem hilbertTensorFamily_apply (h : OneParticleSpace I) (f : E) (i : I) :
    hilbertTensorFamily h f i = h i • f := rfl

theorem inner_hilbertTensorFamily (h k : OneParticleSpace I) (f g : E) :
    inner ℂ (hilbertTensorFamily h f) (hilbertTensorFamily k g) =
      inner ℂ h k * inner ℂ f g := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  simp only [hilbertTensorFamily_apply, inner_smul_left, inner_smul_right]
  simp_rw [← mul_assoc]
  rw [← tsum_mul_right]
  congr 1

/-- The elementary tensor map is bilinear, with the genuine Hilbert norms. -/
def hilbertTensorBilinear : OneParticleSpace I →ₗ[ℂ] E →ₗ[ℂ] lp (fun _ : I => E) 2 where
  toFun h :=
    { toFun := hilbertTensorFamily h
      map_add' := by intros; ext i; simp [smul_add]
      map_smul' := by intros; ext i; simp [smul_smul, mul_comm] }
  map_add' := by intros; ext f i; simp [add_smul]
  map_smul' := by intros; ext f i; simp [smul_smul]

/-- The algebraic Hilbert tensor embeds into the completed family space. -/
def hilbertTensorLift : (OneParticleSpace I ⊗[ℂ] E) →ₗ[ℂ] lp (fun _ : I => E) 2 :=
  TensorProduct.lift hilbertTensorBilinear

@[simp] theorem hilbertTensorLift_tmul (h : OneParticleSpace I) (f : E) :
    hilbertTensorLift (h ⊗ₜ[ℂ] f) = hilbertTensorFamily h f := rfl

/-- The lift preserves the inner product on all finite sums of elementary tensors. -/
theorem inner_hilbertTensorLift (x y : OneParticleSpace I ⊗[ℂ] E) :
    inner ℂ (hilbertTensorLift x) (hilbertTensorLift y) = inner ℂ x y := by
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp only [map_add, inner_add_left, hx, hz]
  | tmul h f =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, inner_add_right, hy, hz]
    | tmul k g => rw [hilbertTensorLift_tmul, hilbertTensorLift_tmul,
        inner_hilbertTensorFamily, TensorProduct.inner_tmul]

/-- No kernel of the algebraic tensor embedding is hidden by completion. -/
def hilbertTensorIsometry : (OneParticleSpace I ⊗[ℂ] E) →ₗᵢ[ℂ] lp (fun _ : I => E) 2 :=
  hilbertTensorLift.isometryOfInner inner_hilbertTensorLift

variable [CompleteSpace E]

/-- The genuine continuous extension from the Hilbert completion. -/
def completedTensorMap : Completion (OneParticleSpace I ⊗[ℂ] E) →L[ℂ] lp (fun _ : I => E) 2 :=
  hilbertTensorIsometry.toContinuousLinearMap.fromCompletion

@[simp] theorem completedTensorMap_coe (x : OneParticleSpace I ⊗[ℂ] E) :
    completedTensorMap (x : Completion (OneParticleSpace I ⊗[ℂ] E)) = hilbertTensorLift x :=
  ContinuousLinearMap.fromCompletion_apply_coe _ x

theorem norm_completedTensorMap (x : Completion (OneParticleSpace I ⊗[ℂ] E)) :
    ‖completedTensorMap x‖ = ‖x‖ := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) continuous_norm
  | ih x => rw [completedTensorMap_coe, Completion.norm_coe]; exact hilbertTensorIsometry.norm_map x

/-- The completed tensor map is still exactly isometric. -/
def completedTensorIsometry : Completion (OneParticleSpace I ⊗[ℂ] E) →ₗᵢ[ℂ] lp (fun _ : I => E) 2 :=
  { completedTensorMap.toLinearMap with norm_map' := norm_completedTensorMap }

omit [CompleteSpace E] in
@[simp] theorem hilbertTensorFamily_single (i : I) (f : E) :
    hilbertTensorFamily (lp.single 2 i (1 : ℂ)) f = lp.single 2 i f := by
  ext j
  simp only [hilbertTensorFamily_apply, lp.single_apply, Pi.single_apply]
  by_cases h : j = i <;> simp [h]

/-- Completion is essential: the extended map, rather than its algebraic restriction, is onto. -/
theorem completedTensorIsometry_surjective :
    Function.Surjective (completedTensorIsometry (I := I) (E := E)) := by
  have hc : IsClosed (Set.range (completedTensorIsometry (I := I) (E := E))) :=
    completedTensorIsometry.isometry.isUniformInducing.isComplete_range.isClosed
  intro f
  have hs := lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) f
  apply hc.mem_of_tendsto hs
  apply Filter.Eventually.of_forall
  intro s
  change (∑ i ∈ s, lp.single 2 i (f i)) ∈ LinearMap.range completedTensorIsometry.toLinearMap
  apply Submodule.sum_mem
  intro i hi
  refine ⟨((lp.single 2 i (1 : ℂ)) ⊗ₜ[ℂ] f i : OneParticleSpace I ⊗[ℂ] E), ?_⟩
  change completedTensorMap _ = _
  rw [completedTensorMap_coe, hilbertTensorLift_tmul, hilbertTensorFamily_single]

/-- The completed Hilbert tensor is exactly the external Hilbert sum. -/
def completedTensorEquiv : Completion (OneParticleSpace I ⊗[ℂ] E) ≃ₗᵢ[ℂ] lp (fun _ : I => E) 2 :=
  LinearIsometryEquiv.ofSurjective completedTensorIsometry completedTensorIsometry_surjective

end FreeProbability.Fock

import FreeProbability.Fock.FiniteDepthPropagation
import FreeProbability.Fock.SecondQuantizationCompressionMatrix
import FreeProbability.OperatorValued.MatrixPencilResolvent

/-! # Actual matrix Fock pencil propagation and depth compression -/
noncomputable section
open scoped Classical InnerProductSpace ENNReal
namespace FreeProbability.Fock
variable {I n : Type*} [Fintype I] [Fintype n] [DecidableEq n]

/-- The literal matrix depth space in the complete finite Hilbert sum. -/
def matrixDepthSpace (L : ℕ) : Submodule ℂ (HilbertMatrixSpace n (WordSpace I)) where
  carrier := {f | ∀ j, f j ∈ depthSpace L}
  zero_mem' := by intro j; exact Submodule.zero_mem _
  add_mem' := by intro f g hf hg j; exact Submodule.add_mem _ (hf j) (hg j)
  smul_mem' := by intro c f hf j; exact Submodule.smul_mem _ c (hf j)

/-- The genuine diagonal finite-depth projection on the matrix Fock Hilbert space. -/
def matrixDepthProjection (L : ℕ) :
    HilbertMatrixSpace n (WordSpace I) →L[ℂ] HilbertMatrixSpace n (WordSpace I) :=
  hilbertMatrixOperator (Matrix.diagonal fun _ : n => depthProjection (I := I) L)

@[simp] theorem matrixDepthProjection_apply (L : ℕ) (f : HilbertMatrixSpace n (WordSpace I)) (j : n) :
    matrixDepthProjection L f j = depthProjection L (f j) := by
  unfold matrixDepthProjection
  rw [hilbertMatrixOperator_apply, Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    simp [Ne.symm hkj]
  · simp

theorem matrixDepthProjection_eq_self_iff (L : ℕ) (f : HilbertMatrixSpace n (WordSpace I)) :
    matrixDepthProjection L f = f ↔ f ∈ matrixDepthSpace L := by
  constructor
  · intro h j
    apply (depthProjection_eq_self_iff L (f j)).mp
    simpa only [matrixDepthProjection_apply] using congrArg (fun g : HilbertMatrixSpace n (WordSpace I) => g j) h
  · intro h
    apply lp.ext
    funext j
    rw [matrixDepthProjection_apply]
    exact (depthProjection_eq_self_iff L (f j)).mpr (h j)

theorem norm_matrixDepthProjection_apply_le (L : ℕ) (f : HilbertMatrixSpace n (WordSpace I)) :
    ‖matrixDepthProjection L f‖ ≤ ‖f‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro j
  rw [matrixDepthProjection_apply]
  exact norm_finiteWordProjection_apply_le _ _

theorem norm_matrixDepthProjection_le (L : ℕ) :
    ‖matrixDepthProjection (n := n) (I := I) L‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using norm_matrixDepthProjection_apply_le L f

@[simp] theorem matrixDepthProjection_idempotent (L : ℕ) :
    (matrixDepthProjection (n := n) (I := I) L).comp (matrixDepthProjection L) = matrixDepthProjection L := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext j
  simp only [ContinuousLinearMap.comp_apply, matrixDepthProjection_apply]
  exact DFunLike.congr_fun (depthProjection_idempotent L) (f j)

omit [DecidableEq n] in
theorem matrixDepthSpace_finiteDimensional (L : ℕ) :
    FiniteDimensional ℂ (matrixDepthSpace (n := n) (I := I) L) := by
  let : FiniteDimensional ℂ (depthSpace (I := I) L) := finiteWordProjection_finite_span _
  let F : matrixDepthSpace (n := n) (I := I) L →ₗ[ℂ] (∀ j : n, depthSpace (I := I) L) :=
    { toFun := fun f j => ⟨f.val j, f.property j⟩
      map_add' := by intro f g; rfl
      map_smul' := by intro c f; rfl }
  apply FiniteDimensional.of_injective F
  intro f g h
  apply Subtype.ext
  apply lp.ext
  funext j
  exact congrArg Subtype.val (congrFun h j)

theorem matrixDepthProjection_range (L : ℕ) :
    LinearMap.range (matrixDepthProjection (n := n) (I := I) L).toLinearMap = matrixDepthSpace L := by
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    apply (matrixDepthProjection_eq_self_iff L _).mp
    exact DFunLike.congr_fun (matrixDepthProjection_idempotent L) f
  · intro f hf
    exact ⟨f, (matrixDepthProjection_eq_self_iff L f).mpr hf⟩

theorem matrixDepthProjection_finiteDimensional (L : ℕ) :
    FiniteDimensional ℂ (LinearMap.range (matrixDepthProjection (n := n) (I := I) L).toLinearMap) := by
  rw [matrixDepthProjection_range]
  exact matrixDepthSpace_finiteDimensional L

/-- The actual matrix pencil represented as a bounded operator on the complete matrix Hilbert space. -/
def finiteDepthPencilOperator (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ) :
    HilbertMatrixSpace n (WordSpace I) →L[ℂ] HilbertMatrixSpace n (WordSpace I) :=
  hilbertMatrixOperator (scalarMatrixEmbedding C₀ + matrixLinearCombination semicircular C)

theorem finiteDepthPencilOperator_eq_representation (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ) :
    finiteDepthPencilOperator C₀ C = (hilbertMatrixStarAlgEquiv (N := n) (E := WordSpace I)) (operatorMatrixPencil C₀ C) := rfl

@[simp] theorem finiteDepthPencilOperator_apply (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ)
    (f : HilbertMatrixSpace n (WordSpace I)) (j : n) :
    finiteDepthPencilOperator C₀ C f j =
      ∑ k, (C₀ j k • f k + ∑ i, C i j k • semicircular i (f k)) := by
  simp [finiteDepthPencilOperator, hilbertMatrixOperator_apply, matrixLinearCombination,
    scalarMatrixEmbedding_apply, Algebra.algebraMap_eq_smul_one]

/-- General matrix coefficients have genuine depth-one propagation; no Hermitian or positivity premise is needed for this structural result. -/
theorem finiteDepthPencilOperator_mem_depth (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ)
    (L : ℕ) {f : HilbertMatrixSpace n (WordSpace I)} (hf : f ∈ matrixDepthSpace L) :
    finiteDepthPencilOperator C₀ C f ∈ matrixDepthSpace (L + 1) := by
  intro j
  rw [finiteDepthPencilOperator_apply]
  apply Submodule.sum_mem
  intro k _
  apply Submodule.add_mem
  · exact Submodule.smul_mem _ _ (depthSpace_mono (Nat.le_succ L) (hf k))
  · apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (semicircular_mem_depthSpace i L (hf k))

end FreeProbability.Fock

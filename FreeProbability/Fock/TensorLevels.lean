import FreeProbability.Fock.TensorCompletion

/-!
# Exact completed tensor recursion for the word levels

The zeroth level is the scalar Hilbert space, and the next level is the genuine
Hilbert completion of the tensor product of the one-particle space with the
previous level. Together with `lengthDecomposition`, these equivalences identify
the word model as the Hilbert sum of recursively completed tensor levels.
-/

noncomputable section
open scoped Classical InnerProductSpace TensorProduct ENNReal
open UniformSpace

namespace FreeProbability.Fock

variable {I : Type*}

/-- The unique empty tuple indexes the scalar vacuum level. -/
def emptyTuple : Fin 0 → I := Fin.elim0

/-- Exact isometric scalar inclusion into the zeroth tensor level. -/
def scalarLevelIsometry : ℂ →ₗᵢ[ℂ] WordLevel I 0 :=
  LinearIsometry.toSpanSingleton ℂ (WordLevel I 0) (by
    simp [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)] :
      ‖lp.single 2 (emptyTuple : Fin 0 → I) (1 : ℂ)‖ = 1)

theorem scalarLevelIsometry_surjective : Function.Surjective (scalarLevelIsometry (I := I)) := by
  intro f
  refine ⟨f emptyTuple, ?_⟩
  ext a
  have ha : a = emptyTuple := Subsingleton.elim _ _
  subst a
  simp [scalarLevelIsometry, LinearIsometry.toSpanSingleton_apply, lp.single_apply]

/-- The zeroth completed tensor level is exactly the scalar Hilbert space. -/
def scalarLevelEquiv : ℂ ≃ₗᵢ[ℂ] WordLevel I 0 :=
  LinearIsometryEquiv.ofSurjective scalarLevelIsometry scalarLevelIsometry_surjective

/-- Canonical scalar basis of each complete word level. -/
def levelWord (n : ℕ) (a : Fin n → I) : WordLevel I n := lp.single 2 a 1

@[simp] theorem inner_levelWord (n : ℕ) (a b : Fin n → I) :
    inner ℂ (levelWord n a) (levelWord n b) = if a = b then 1 else 0 := by
  simp [levelWord, lp.inner_single_left, lp.single_apply, Pi.single_apply]

theorem orthonormal_levelWord (n : ℕ) : Orthonormal ℂ (levelWord (I := I) n) := by
  rw [orthonormal_iff_ite]
  exact inner_levelWord n

theorem orthonormal_levelPrefix (n : ℕ) (i : I) :
    Orthonormal ℂ (fun a : Fin n → I => levelWord (n + 1) (Fin.cons i a)) := by
  rw [orthonormal_iff_ite]
  intro a b
  rw [inner_levelWord]
  have he : (Fin.cons i a : Fin (n + 1) → I) = Fin.cons i b ↔ a = b := by
    constructor
    · intro h; funext j; simpa using congrFun h j.succ
    · intro h; rw [h]
  simp only [he]

/-- The complete level inclusion obtained by prefixing a basis letter. -/
def levelPrefix (n : ℕ) (i : I) : WordLevel I n →ₗᵢ[ℂ] WordLevel I (n + 1) :=
  (orthonormal_levelPrefix n i).orthogonalFamily.linearIsometry

@[simp] theorem levelPrefix_single (n : ℕ) (i : I) (a : Fin n → I) (c : ℂ) :
    levelPrefix n i (lp.single 2 a c) = c • levelWord (n + 1) (Fin.cons i a) := by
  rw [levelPrefix, OrthogonalFamily.linearIsometry_apply_single]
  simp [LinearIsometry.toSpanSingleton_apply]

theorem hasSum_levelPrefix (n : ℕ) (i : I) (f : WordLevel I n) :
    HasSum (fun a => f a • levelWord (n + 1) (Fin.cons i a)) (levelPrefix n i f) := by
  simpa only [levelPrefix, LinearIsometry.toSpanSingleton_apply] using
    (orthonormal_levelPrefix n i).orthogonalFamily.hasSum_linearIsometry f

theorem orthogonal_levelPrefix (n : ℕ) :
    OrthogonalFamily ℂ (fun _ : I => ↥(WordLevel I n)) (fun i => levelPrefix n i) := by
  intro i j hij f g
  have hword (a : Fin n → I) :
      inner ℂ (levelWord (n + 1) (Fin.cons i a)) (levelPrefix n j g) = 0 := by
    have hs := (innerSL ℂ (levelWord (n + 1) (Fin.cons i a))).hasSum (hasSum_levelPrefix n j g)
    have ht (b : Fin n → I) : inner ℂ (levelWord (n + 1) (Fin.cons i a))
        (g b • levelWord (n + 1) (Fin.cons j b)) = 0 := by
      have hne : (Fin.cons i a : Fin (n + 1) → I) ≠ Fin.cons j b := by
        intro h
        apply hij
        simpa using congrFun h 0
      rw [inner_smul_right, inner_levelWord]
      simp only [hne, ite_false, mul_zero]
    simp only [innerSL_apply_apply, ht] at hs
    exact hs.unique hasSum_zero
  have hs := (innerSL ℂ (levelPrefix n j g)).hasSum (hasSum_levelPrefix n i f)
  have ht (a : Fin n → I) : inner ℂ (levelPrefix n j g)
      (f a • levelWord (n + 1) (Fin.cons i a)) = 0 := by
    rw [inner_smul_right, ← inner_conj_symm, hword]
    simp
  simp only [innerSL_apply_apply, ht] at hs
  rw [← inner_conj_symm, hs.unique hasSum_zero]
  simp

/-- Every vector in the next level lies in the closed span of prefixed previous levels. -/
theorem levelPrefix_total (n : ℕ) :
    ⊤ ≤ (⨆ i, LinearMap.range (levelPrefix (I := I) n i).toLinearMap).topologicalClosure := by
  intro f _
  have hc := (⨆ i, LinearMap.range (levelPrefix (I := I) n i).toLinearMap).isClosed_topologicalClosure
  apply hc.mem_of_tendsto (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) f)
  apply Filter.Eventually.of_forall
  intro s
  apply Submodule.sum_mem
  intro a ha
  apply Submodule.le_topologicalClosure
  apply (le_iSup (fun i => LinearMap.range (levelPrefix (I := I) n i).toLinearMap) (a 0))
  refine ⟨lp.single 2 (Fin.tail a) (f a), ?_⟩
  change levelPrefix n (a 0) (lp.single 2 (Fin.tail a) (f a)) = lp.single 2 a (f a)
  rw [levelPrefix_single, Fin.cons_self_tail]
  simp [levelWord, ← lp.single_smul]

/-- The next length level is the actual external Hilbert sum of previous levels. -/
theorem successorLevel_isHilbertSum (n : ℕ) :
    IsHilbertSum ℂ (fun _ : I => ↥(WordLevel I n)) (fun i => levelPrefix n i) :=
  IsHilbertSum.mk (orthogonal_levelPrefix n) (levelPrefix_total n)

/-- Exact tensor recursion, using the Hilbert completion rather than algebraic completeness. -/
def successorLevelTensorEquiv (n : ℕ) :
    Completion (OneParticleSpace I ⊗[ℂ] WordLevel I n) ≃ₗᵢ[ℂ] WordLevel I (n + 1) :=
  completedTensorEquiv.trans (successorLevel_isHilbertSum n).linearIsometryEquiv.symm

@[simp] theorem successorLevelTensorEquiv_basis_tmul (n : ℕ) (i : I) (f : WordLevel I n) :
    successorLevelTensorEquiv n
      ((lp.single 2 i (1 : ℂ) ⊗ₜ[ℂ] f : OneParticleSpace I ⊗[ℂ] WordLevel I n) :
        Completion (OneParticleSpace I ⊗[ℂ] WordLevel I n)) = levelPrefix n i f := by
  change (successorLevel_isHilbertSum n).linearIsometryEquiv.symm (completedTensorMap _) = _
  rw [completedTensorMap_coe, hilbertTensorLift_tmul, hilbertTensorFamily_single]
  exact (successorLevel_isHilbertSum n).linearIsometryEquiv_symm_apply_single f

/-- Prefixing in the genuine tensor level agrees with bounded word creation. -/
theorem levelEmbedding_prefix (n : ℕ) (i : I) (f : WordLevel I n) :
    levelEmbedding (n + 1) (levelPrefix n i f) = creation i (levelEmbedding n f) := by
  have he : (levelEmbedding (I := I) (n + 1)).toContinuousLinearMap.comp
      (levelPrefix n i).toContinuousLinearMap =
      (creation i).comp (levelEmbedding n).toContinuousLinearMap := by
    apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    intro a
    apply ContinuousLinearMap.ext
    intro c
    simp [levelPrefix_single, levelWord, levelEmbedding_single,
      creation_word, map_smul]
  exact congrArg (fun T : WordLevel I n →L[ℂ] WordSpace I => T f) he

/-- Creation by every one-particle vector is literal tensoring on each completed level. -/
theorem levelEmbedding_tensorCreation (n : ℕ) (h : OneParticleSpace I) (f : WordLevel I n) :
    levelEmbedding (n + 1) (successorLevelTensorEquiv n
      ((h ⊗ₜ[ℂ] f : OneParticleSpace I ⊗[ℂ] WordLevel I n) :
        Completion (OneParticleSpace I ⊗[ℂ] WordLevel I n))) =
      vectorCreation h (levelEmbedding n f) := by
  have hl := (levelEmbedding (I := I) (n + 1)).toContinuousLinearMap.hasSum
    ((successorLevel_isHilbertSum n).hasSum_linearIsometryEquiv_symm (hilbertTensorFamily h f))
  have hr := orthogonal_creationFamily.hasSum_linearIsometry (tensorVector h (levelEmbedding n f))
  change HasSum (fun i => levelEmbedding (n + 1) (levelPrefix n i (hilbertTensorFamily h f i)))
    (levelEmbedding (n + 1) ((successorLevel_isHilbertSum n).linearIsometryEquiv.symm
      (hilbertTensorFamily h f))) at hl
  change HasSum (fun i => creation i (tensorVector h (levelEmbedding n f) i))
    (vectorCreation h (levelEmbedding n f)) at hr
  simp only [hilbertTensorFamily_apply, map_smul, levelEmbedding_prefix] at hl
  simp only [tensorVector_apply, map_smul] at hr
  have he := hl.unique hr
  change levelEmbedding (n + 1)
    ((successorLevel_isHilbertSum n).linearIsometryEquiv.symm (completedTensorMap _)) = _
  rw [completedTensorMap_coe, hilbertTensorLift_tmul]
  exact he

end FreeProbability.Fock

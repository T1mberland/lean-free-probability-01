import FreeProbability.Fock.FiniteDepthPencilResolvent

/-! # True operator-norm error for finite-depth matrix vacuum compression -/
noncomputable section
open scoped Classical Ring ENNReal
namespace FreeProbability.Fock
variable {I n : Type*} [Fintype I] [Fintype n] [DecidableEq n]

/-- The literal finite Hilbert-sum vacuum inclusion, with a proved norm bound. -/
def matrixVacuumInclusion : HilbertMatrixSpace n ℂ →L[ℂ] HilbertMatrixSpace n (WordSpace I) :=
  LinearMap.mkContinuous
    { toFun := fun v => ⟨fun j => v j • vacuum, Memℓp.all _⟩
      map_add' := by
        intro v w
        apply lp.ext
        funext j
        change (v j + w j) • vacuum = v j • vacuum + w j • vacuum
        exact add_smul _ _ _
      map_smul' := by intro c v; apply lp.ext; funext j; simp [smul_smul] }
    1 (by
      intro v
      change ‖(⟨fun j => v j • (vacuum : WordSpace I), Memℓp.all _⟩ :
        HilbertMatrixSpace n (WordSpace I))‖ ≤ 1 * ‖v‖
      rw [one_mul]
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro j
      simp [norm_smul])

omit [Fintype I] [DecidableEq n] in
@[simp] theorem matrixVacuumInclusion_apply (v : HilbertMatrixSpace n ℂ) (j : n) :
    matrixVacuumInclusion (I := I) v j = v j • vacuum := rfl

omit [DecidableEq n] in
theorem matrixVacuumInclusion_mem_depth_zero (v : HilbertMatrixSpace n ℂ) :
    matrixVacuumInclusion (I := I) v ∈ matrixDepthSpace 0 := by
  intro j
  exact Submodule.smul_mem _ _ (word_mem_depthSpace [] (by simp))

omit [Fintype I] [DecidableEq n] in
theorem norm_matrixVacuumInclusion_apply (v : HilbertMatrixSpace n ℂ) :
    ‖matrixVacuumInclusion (I := I) v‖ = ‖v‖ := by
  apply le_antisymm
  · apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro j
    simp [norm_smul]
  · apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro j
    simp [norm_smul]

omit [Fintype I] [DecidableEq n] in
theorem norm_matrixVacuumInclusion_le : ‖matrixVacuumInclusion (n := n) (I := I)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simp [norm_matrixVacuumInclusion_apply]

/-- Actual compression on the finite coefficient Hilbert space, with its operator norm. -/
def matrixVacuumCompression (T : HilbertMatrixSpace n (WordSpace I) →L[ℂ]
    HilbertMatrixSpace n (WordSpace I)) : HilbertMatrixSpace n ℂ →L[ℂ] HilbertMatrixSpace n ℂ :=
  (matrixVacuumInclusion (n := n) (I := I)).adjoint.comp
    (T.comp matrixVacuumInclusion)

variable [Nonempty n]

/-- A genuine matrix operator-norm estimate, obtained from all coefficient vectors. -/
theorem finiteDepthPencilVacuumCompression_error (C₀ : Matrix n n ℂ)
    (C : I → Matrix n n ℂ) (hC₀ : C₀.IsHermitian) (hC : ∀ i, (C i).IsHermitian)
    (L : ℕ) (z : ℝ) (hz : finiteDepthPencilUpperEdge C₀ C < z) :
    ‖matrixVacuumCompression (((z : ℂ) • 1 - finiteDepthPencilOperator C₀ C)⁻¹ʳ) -
        matrixVacuumCompression (finiteDepthPencilResolvent C₀ C L z)‖ ≤
      2 * ((finiteDepthPencilUpperEdge C₀ C + ‖finiteDepthPencilOperator C₀ C‖) /
        (z + ‖finiteDepthPencilOperator C₀ C‖)) ^ (L + 1) /
        (z - finiteDepthPencilUpperEdge C₀ C) := by
  let K := 2 * ((finiteDepthPencilUpperEdge C₀ C + ‖finiteDepthPencilOperator C₀ C‖) /
        (z + ‖finiteDepthPencilOperator C₀ C‖)) ^ (L + 1) /
        (z - finiteDepthPencilUpperEdge C₀ C)
  have hR := finiteDepthPencilUpperEdge_add_norm_nonneg C₀ C hC₀ hC
  have hd : 0 < z + ‖finiteDepthPencilOperator C₀ C‖ := by
    linarith
  have hK : 0 ≤ K := by
    exact div_nonneg (mul_nonneg (by norm_num)
      (pow_nonneg (div_nonneg hR hd.le) _)) (sub_pos.mpr hz).le
  apply ContinuousLinearMap.opNorm_le_bound _ hK
  intro v
  change ‖(matrixVacuumInclusion (n := n) (I := I)).adjoint
      (((z : ℂ) • 1 - finiteDepthPencilOperator C₀ C)⁻¹ʳ (matrixVacuumInclusion v)) -
      (matrixVacuumInclusion (n := n) (I := I)).adjoint
      (finiteDepthPencilResolvent C₀ C L z (matrixVacuumInclusion v))‖ ≤ K * ‖v‖
  rw [← map_sub]
  have hJ : ‖(matrixVacuumInclusion (n := n) (I := I)).adjoint‖ ≤ 1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact norm_matrixVacuumInclusion_le
  calc
    _ ≤ 1 * ‖((z : ℂ) • 1 - finiteDepthPencilOperator C₀ C)⁻¹ʳ
        (matrixVacuumInclusion v) - finiteDepthPencilResolvent C₀ C L z
        (matrixVacuumInclusion v)‖ :=
      (matrixVacuumInclusion (n := n) (I := I)).adjoint.le_of_opNorm_le hJ _
    _ ≤ K * ‖matrixVacuumInclusion (I := I) v‖ := by
      rw [one_mul]
      exact finiteDepthPencilResolvent_error C₀ C hC₀ hC L z hz
        (matrixVacuumInclusion_mem_depth_zero v)
    _ = K * ‖v‖ := by rw [norm_matrixVacuumInclusion_apply]

end FreeProbability.Fock

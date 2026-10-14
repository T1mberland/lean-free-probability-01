import FreeProbability.Fock.SecondQuantizationCompressionMatrix

/-! # Genuine complete positivity of second-quantized operator compression -/
noncomputable section
open scoped Classical InnerProductSpace CStarAlgebra ENNReal

namespace FreeProbability.Fock
section Amplification
variable {N E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Coordinate amplification of a genuine Hilbert isometry to a Hilbert sum. -/
def hilbertIsometryAmplification (N : Type*) (W : E →ₗᵢ[ℂ] F) :
    HilbertMatrixSpace N E →ₗᵢ[ℂ] HilbertMatrixSpace N F where
  toFun f := ⟨fun i => W (f i), by
    apply Memℓp.of_norm
    simpa only [W.norm_map] using (lp.memℓp f).norm⟩
  map_add' f g := by ext i; simp; rfl
  map_smul' c f := by ext i; simp
  norm_map' f := by
    rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal),
      lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    congr 1
    congr 1
    funext i
    exact congrArg (fun r : ℝ => r ^ (2 : ℝ≥0∞).toReal) (W.norm_map (f i))

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem hilbertIsometryAmplification_degree (W : E →ₗᵢ[ℂ] F)
    (f : HilbertMatrixSpace N E) (i : N) : hilbertIsometryAmplification N W f i = W (f i) := rfl

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem hilbertIsometryAmplification_single (W : E →ₗᵢ[ℂ] F) (i : N) (x : E) :
    hilbertIsometryAmplification N W (lp.single 2 i x) = lp.single 2 i (W x) := by
  ext j
  by_cases hj : j = i
  · subst j; simp [lp.single_apply]
  · simp [lp.single_apply, hj]

/-- The genuine Hilbert adjoint of the amplification acts coordinatewise. -/
theorem hilbertIsometryAmplification_adjoint_degree (W : E →ₗᵢ[ℂ] F)
    (f : HilbertMatrixSpace N F) (i : N) :
    (hilbertIsometryAmplification N W).toContinuousLinearMap.adjoint f i =
      W.toContinuousLinearMap.adjoint (f i) := by
  apply ext_inner_left ℂ
  intro x
  calc
    inner ℂ x ((hilbertIsometryAmplification N W).toContinuousLinearMap.adjoint f i) =
      inner ℂ (lp.single 2 i x) ((hilbertIsometryAmplification N W).toContinuousLinearMap.adjoint f) :=
      (lp.inner_single_left (𝕜 := ℂ) i x
        ((hilbertIsometryAmplification N W).toContinuousLinearMap.adjoint f)).symm
    _ = inner ℂ (hilbertIsometryAmplification N W (lp.single 2 i x)) f :=
      (ContinuousLinearMap.adjoint_inner_right _ _ _)
    _ = inner ℂ (lp.single 2 i (W x)) f := by rw [hilbertIsometryAmplification_single]
    _ = inner ℂ (W x) (f i) := lp.inner_single_left (𝕜 := ℂ) i (W x) f
    _ = inner ℂ x (W.toContinuousLinearMap.adjoint (f i)) :=
      (W.toContinuousLinearMap.adjoint_inner_right x (f i)).symm
end Amplification

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Entrywise compression is precisely actual block-operator compression at each finite level. -/
theorem secondQuantizationCompression_matrix_realization {N : Type*} [Fintype N]
    (V : H →ₗᵢ[ℂ] K) (M : CStarMatrix N N (TensorFullFock K →L[ℂ] TensorFullFock K)) :
    (hilbertMatrixStarAlgEquiv (N := N) (E := TensorFullFock H))
      (M.map (secondQuantizationCompression V)) =
    (hilbertIsometryAmplification N (secondQuantizationIsometry V)).toContinuousLinearMap.adjoint.comp
      (((hilbertMatrixStarAlgEquiv (N := N) (E := TensorFullFock K)) M).comp
        (hilbertIsometryAmplification N (secondQuantizationIsometry V)).toContinuousLinearMap) := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext i
  change hilbertMatrixOperator (CStarMatrix.ofMatrix.symm
      (M.map (secondQuantizationCompression V))) f i = _
  rw [hilbertMatrixOperator_apply]
  change (∑ j, (secondQuantizationIsometry V).toContinuousLinearMap.adjoint
    ((CStarMatrix.ofMatrix.symm M i j) (secondQuantizationIsometry V (f j)))) =
      (hilbertIsometryAmplification N (secondQuantizationIsometry V)).toContinuousLinearMap.adjoint
        (hilbertMatrixOperator (CStarMatrix.ofMatrix.symm M)
          (hilbertIsometryAmplification N (secondQuantizationIsometry V) f)) i
  rw [hilbertIsometryAmplification_adjoint_degree, hilbertMatrixOperator_apply, map_sum]
  rfl

/-- Genuine positivity for arbitrary positive C-star matrices at every finite level. -/
theorem secondQuantizationCompression_matrix_nonneg {N : Type*} [Fintype N]
    (V : H →ₗᵢ[ℂ] K) (M : CStarMatrix N N (TensorFullFock K →L[ℂ] TensorFullFock K))
    (hM : 0 ≤ M) : 0 ≤ M.map (secondQuantizationCompression V) := by
  apply (hilbertMatrixStarAlgEquiv_nonneg_iff _).mp
  rw [secondQuantizationCompression_matrix_realization]
  apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
  exact (ContinuousLinearMap.nonneg_iff_isPositive.mp
    (hilbertMatrixStarAlgEquiv_nonneg M hM)).adjoint_conj _

/-- The actual compression as a bundled completely positive linear map. -/
def secondQuantizationCompressionCP (V : H →ₗᵢ[ℂ] K) :
    (TensorFullFock K →L[ℂ] TensorFullFock K) →CP
      (TensorFullFock H →L[ℂ] TensorFullFock H) where
  toLinearMap := secondQuantizationCompression V
  map_cstarMatrix_nonneg' _k M hM := secondQuantizationCompression_matrix_nonneg V M hM

@[simp] theorem secondQuantizationCompressionCP_one (V : H →ₗᵢ[ℂ] K) :
    secondQuantizationCompressionCP V 1 = 1 := secondQuantizationCompression_one V

end FreeProbability.Fock

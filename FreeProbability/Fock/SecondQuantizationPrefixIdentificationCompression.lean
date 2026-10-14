import FreeProbability.Fock.SecondQuantizationPrefixIdentificationSector

/-! # Full bounded-operator intertwining and actual compression left inverse -/
noncomputable section
open scoped Classical
namespace FreeProbability.Fock
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Actual representation intertwines Γ(V) for EVERY source bounded operator. -/
theorem isometryPrefixEmbedding_inclusion (V : H →ₗᵢ[ℂ] K)
    (T : TensorFullFock H →L[ℂ] TensorFullFock H) (f : TensorFullFock H) :
    isometryPrefixEmbedding V T (secondQuantizationIsometry V f) =
      secondQuantizationIsometry V (T f) := by
  rw [secondQuantizationIsometry_prefix_sector, secondQuantizationIsometry_prefix_sector]
  change isometryPrefixTargetUnitary V
    (prefixOperatorEmbedding ((fullFockTensorDecomposition H).symm.conjStarAlgEquiv T)
      ((isometryPrefixTargetUnitary V).symm
        (isometryPrefixTargetUnitary V
          (prefixTailEmbedding none ((fullFockTensorDecomposition H).symm f))))) = _
  rw [LinearIsometryEquiv.symm_apply_apply, prefixOperatorEmbedding_sector]
  change isometryPrefixTargetUnitary V
    (prefixTailEmbedding none ((fullFockTensorDecomposition H).symm
      (T (fullFockTensorDecomposition H ((fullFockTensorDecomposition H).symm f))))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]

theorem isometryPrefixEmbedding_inclusion_comp (V : H →ₗᵢ[ℂ] K)
    (T : TensorFullFock H →L[ℂ] TensorFullFock H) :
    (isometryPrefixEmbedding V T).comp (secondQuantizationIsometry V).toContinuousLinearMap =
      (secondQuantizationIsometry V).toContinuousLinearMap.comp T :=
  ContinuousLinearMap.ext (isometryPrefixEmbedding_inclusion V T)

/-- Actual full compression is a left inverse of the representation on ALL source bounded operators. -/
theorem isometryPrefixEmbedding_compression (V : H →ₗᵢ[ℂ] K)
    (T : TensorFullFock H →L[ℂ] TensorFullFock H) :
    secondQuantizationCompression V (isometryPrefixEmbedding V T) = T := by
  change (secondQuantizationIsometry V).toContinuousLinearMap.adjoint.comp
    ((isometryPrefixEmbedding V T).comp (secondQuantizationIsometry V).toContinuousLinearMap) = _
  rw [isometryPrefixEmbedding_inclusion_comp, ← ContinuousLinearMap.comp_assoc,
    secondQuantizationIsometry_adjoint_comp]
  rfl

/-- The representation sends the vacuum orbit of every bounded operator to its actual Γ(V) orbit. -/
theorem isometryPrefixEmbedding_vacuum (V : H →ₗᵢ[ℂ] K)
    (T : TensorFullFock H →L[ℂ] TensorFullFock H) :
    isometryPrefixEmbedding V T (tensorVacuum K) =
      secondQuantizationIsometry V (T (tensorVacuum H)) := by
  have h := isometryPrefixEmbedding_inclusion V T (tensorVacuum H)
  rw [secondQuantizationIsometry_vacuum] at h
  exact h

/-- Actual normalized ambient vacuum states correspond on the entire bounded-operator representation. -/
theorem isometryPrefixEmbedding_vacuum_expectation (V : H →ₗᵢ[ℂ] K)
    (T : TensorFullFock H →L[ℂ] TensorFullFock H) :
    (tensorVacuumState K).expectation (isometryPrefixEmbedding V T) =
      (tensorVacuumState H).expectation T := by
  have h := secondQuantizationCompression_vacuum_expectation V (isometryPrefixEmbedding V T)
  rw [isometryPrefixEmbedding_compression] at h
  rw [tensorVacuumState_expectation, tensorVacuumState_expectation]
  exact h.symm

end FreeProbability.Fock

import FreeProbability.Fock.SecondQuantizationSuffixEmbedding

/-! # Actual all-operator suffix intertwining and compression left inverse -/
noncomputable section
open scoped Classical
namespace FreeProbability.Fock
attribute [local irreducible] fullFockTensorDecomposition isometryPrefixTargetUnitary
section General
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem suffixConjugate_intertwining (R : E ≃ₗᵢ[ℂ] E) (S : F ≃ₗᵢ[ℂ] F)
    (W : E →ₗᵢ[ℂ] F) (Φ : (E →L[ℂ] E) →⋆ₐ[ℂ] (F →L[ℂ] F))
    (hR : ∀ x, R (R x) = x) (hS : ∀ y, S.symm y = S y)
    (hSW : ∀ x, S (W x) = W (R x))
    (hΦ : ∀ T x, Φ T (W x) = W (T x)) (T : E →L[ℂ] E) (x : E) :
    S (Φ (R.conjStarAlgEquiv T) (S.symm (W x))) = W (T x) := by
  rw [hS, hSW, hΦ, hSW]
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_apply_apply, hR]
end General

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem isometrySuffixEmbedding_apply (V : H →ₗᵢ[ℂ] K)
    (T : TensorFullFock H →L[ℂ] TensorFullFock H) (f : TensorFullFock K) :
    isometrySuffixEmbedding V T f = suffixTargetReversal V
      (isometryPrefixEmbedding V ((suffixSourceReversal (H := H)).conjStarAlgEquiv T)
        ((suffixTargetReversal V).symm f)) := by
  rw [isometrySuffixEmbedding, StarAlgHom.comp_apply, StarAlgHom.comp_apply]
  exact LinearIsometryEquiv.conjStarAlgEquiv_apply_apply (suffixTargetReversal V)
    (isometryPrefixEmbedding V ((suffixSourceReversal (H := H)).conjStarAlgEquiv T)) f

/-- Every actual suffix-represented source bounded operator intertwines Γ(V). -/
theorem isometrySuffixEmbedding_inclusion (V : H →ₗᵢ[ℂ] K)
    (T : TensorFullFock H →L[ℂ] TensorFullFock H) (f : TensorFullFock H) :
    isometrySuffixEmbedding V T (secondQuantizationIsometry V f) =
      secondQuantizationIsometry V (T f) := by
  rw [isometrySuffixEmbedding_apply]
  exact suffixConjugate_intertwining (E := TensorFullFock H) (F := TensorFullFock K)
    (suffixSourceReversal (H := H)) (suffixTargetReversal V)
    (secondQuantizationIsometry V) (isometryPrefixEmbedding V)
    (transportedWordReversal_involutive (fullFockTensorDecomposition H))
    (transportedWordReversal_symm_apply (isometryPrefixTargetUnitary V))
    (suffixTargetReversal_inclusion V) (isometryPrefixEmbedding_inclusion V) T f

theorem isometrySuffixEmbedding_inclusion_comp (V : H →ₗᵢ[ℂ] K)
    (T : TensorFullFock H →L[ℂ] TensorFullFock H) :
    (isometrySuffixEmbedding V T).comp (secondQuantizationIsometry V).toContinuousLinearMap =
      (secondQuantizationIsometry V).toContinuousLinearMap.comp T := by
  apply ContinuousLinearMap.ext
  intro f
  change isometrySuffixEmbedding V T (secondQuantizationIsometry V f) = secondQuantizationIsometry V (T f)
  exact isometrySuffixEmbedding_inclusion V T f

/-- Actual full compression recovers every suffix-represented source bounded operator. -/
theorem isometrySuffixEmbedding_compression (V : H →ₗᵢ[ℂ] K)
    (T : TensorFullFock H →L[ℂ] TensorFullFock H) :
    secondQuantizationCompression V (isometrySuffixEmbedding V T) = T := by
  change (secondQuantizationIsometry V).toContinuousLinearMap.adjoint.comp
    ((isometrySuffixEmbedding V T).comp (secondQuantizationIsometry V).toContinuousLinearMap) = _
  rw [isometrySuffixEmbedding_inclusion_comp, ← ContinuousLinearMap.comp_assoc,
    secondQuantizationIsometry_adjoint_comp]
  rfl

/-- Exact ambient vacuum expectation preservation for the suffix representation. -/
theorem isometrySuffixEmbedding_vacuum_expectation (V : H →ₗᵢ[ℂ] K)
    (T : TensorFullFock H →L[ℂ] TensorFullFock H) :
    (tensorVacuumState K).expectation (isometrySuffixEmbedding V T) =
      (tensorVacuumState H).expectation T := by
  have h := secondQuantizationCompression_vacuum_expectation V (isometrySuffixEmbedding V T)
  rw [isometrySuffixEmbedding_compression] at h
  rw [tensorVacuumState_expectation, tensorVacuumState_expectation]
  exact h.symm

end FreeProbability.Fock

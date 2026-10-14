import FreeProbability.Fock.SecondQuantizationSuffixReversal

/-! # Actual suffix amplification through adapted full-space reversal -/
noncomputable section
open scoped Classical ENNReal
namespace FreeProbability.Fock
variable {I : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Actual word reversal transported by a specified complete word-model unitary. -/
def transportedWordReversal (W : WordSpace I ≃ₗᵢ[ℂ] E) : E ≃ₗᵢ[ℂ] E :=
  (W.symm.trans wordReversalUnitary).trans W

omit [CompleteSpace E] in
@[simp] theorem transportedWordReversal_apply (W : WordSpace I ≃ₗᵢ[ℂ] E) (f : E) :
    transportedWordReversal W f = W (reversal (W.symm f)) := rfl

omit [CompleteSpace E] in
@[simp] theorem transportedWordReversal_symm_apply (W : WordSpace I ≃ₗᵢ[ℂ] E) (f : E) :
    (transportedWordReversal W).symm f = transportedWordReversal W f := by
  change W (wordReversalUnitary.symm (W.symm f)) = _
  rw [wordReversalUnitary_symm_apply]
  rfl

omit [CompleteSpace E] in
@[simp] theorem transportedWordReversal_involutive (W : WordSpace I ≃ₗᵢ[ℂ] E) (f : E) :
    transportedWordReversal W (transportedWordReversal W f) = f := by
  rw [transportedWordReversal_apply, transportedWordReversal_apply,
    LinearIsometryEquiv.symm_apply_apply, reversal_reversal, LinearIsometryEquiv.apply_symm_apply]

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Full source reversal in the chosen full source word model. -/
def suffixSourceReversal : TensorFullFock H ≃ₗᵢ[ℂ] TensorFullFock H :=
  transportedWordReversal (fullFockTensorDecomposition H)

/-- Full target reversal in the ACTUAL adapted target word model for this isometry. -/
def suffixTargetReversal (V : H →ₗᵢ[ℂ] K) : TensorFullFock K ≃ₗᵢ[ℂ] TensorFullFock K :=
  transportedWordReversal (isometryPrefixTargetUnitary V)

/-- Genuine unital suffix representation of ALL source bounded operators. -/
def isometrySuffixEmbedding (V : H →ₗᵢ[ℂ] K) :
    (TensorFullFock H →L[ℂ] TensorFullFock H) →⋆ₐ[ℂ]
      (TensorFullFock K →L[ℂ] TensorFullFock K) :=
  (suffixTargetReversal V).conjStarAlgEquiv.toStarAlgHom.comp
    ((isometryPrefixEmbedding V).comp suffixSourceReversal.conjStarAlgEquiv.toStarAlgHom)

theorem isometrySuffixEmbedding_injective (V : H →ₗᵢ[ℂ] K) :
    Function.Injective (isometrySuffixEmbedding V) :=
  (suffixTargetReversal V).conjStarAlgEquiv.injective.comp
    ((isometryPrefixEmbedding_injective V).comp suffixSourceReversal.conjStarAlgEquiv.injective)

/-- Complete empty-tail inclusion intertwines actual word reversal on both full word spaces. -/
theorem reversal_prefixEmpty_comp {I J : Type*} :
    (reversal : WordSpace (Sum I J) →L[ℂ] WordSpace (Sum I J)).comp
      (prefixTailEmbedding none).toContinuousLinearMap =
        (prefixTailEmbedding none).toContinuousLinearMap.comp (reversal : WordSpace I →L[ℂ] WordSpace I) := by
  apply lp.ext_continuousLinearMap (ENNReal.ofNat_ne_top (n := 2))
  intro w
  apply ContinuousLinearMap.ext
  intro c
  have hs : lp.single 2 w c = c • word w := by
    apply lp.ext
    funext v
    simp [word, lp.single_apply, Pi.single_apply]
  change reversal (prefixTailEmbedding none (lp.single 2 w c)) =
    prefixTailEmbedding none (reversal (lp.single 2 w c))
  rw [hs, map_smul, map_smul, identification_prefixTailEmbedding_word, reversal_word]
  rw [map_smul, reversal_word, map_smul, identification_prefixTailEmbedding_word]
  simp [joinPrefixTail, prefixTailWord, List.map_reverse]

/-- Actual adapted target reversal intertwines Γ(V) and source reversal on all completed vectors. -/
theorem suffixTargetReversal_inclusion (V : H →ₗᵢ[ℂ] K) (f : TensorFullFock H) :
    suffixTargetReversal V (secondQuantizationIsometry V f) =
      secondQuantizationIsometry V (suffixSourceReversal f) := by
  rw [secondQuantizationIsometry_prefix_sector, secondQuantizationIsometry_prefix_sector]
  change isometryPrefixTargetUnitary V
    (reversal ((isometryPrefixTargetUnitary V).symm
      (isometryPrefixTargetUnitary V (prefixTailEmbedding none ((fullFockTensorDecomposition H).symm f))))) =
    isometryPrefixTargetUnitary V (prefixTailEmbedding none
      ((fullFockTensorDecomposition H).symm
        (fullFockTensorDecomposition H (reversal ((fullFockTensorDecomposition H).symm f)))))
  rw [LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.symm_apply_apply]
  apply congrArg (isometryPrefixTargetUnitary V)
  exact DFunLike.congr_fun reversal_prefixEmpty_comp ((fullFockTensorDecomposition H).symm f)

end FreeProbability.Fock

import FreeProbability.Fock.SecondQuantizationSuffixDefectWords

/-! # Exact suffix left-creator defect by genuine full-space reversal -/
noncomputable section
open scoped Classical
namespace FreeProbability.Fock
variable {I J : Type*}

theorem reversal_prefixEmpty_sandwich (T : WordSpace I →L[ℂ] WordSpace I) :
    wordReversalUnitary.conjStarAlgEquiv
      ((prefixTailEmbedding (J := J) none).toContinuousLinearMap.comp
        (T.comp (prefixTailEmbedding none).toContinuousLinearMap.adjoint)) =
      (prefixTailEmbedding none).toContinuousLinearMap.comp
        ((wordReversalUnitary.conjStarAlgEquiv T).comp
          (prefixTailEmbedding none).toContinuousLinearMap.adjoint) := by
  have ha := congrArg ContinuousLinearMap.adjoint (reversal_prefixEmpty_comp (I := I) (J := J))
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    adjoint_reversal, adjoint_reversal] at ha
  apply ContinuousLinearMap.ext
  intro f
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    wordReversalUnitary_apply, wordReversalUnitary_symm_apply, ContinuousLinearMap.comp_apply]
  have h1 := DFunLike.congr_fun ha f
  change (prefixTailEmbedding none).toContinuousLinearMap.adjoint (reversal f) =
    reversal ((prefixTailEmbedding none).toContinuousLinearMap.adjoint f) at h1
  rw [h1]
  exact DFunLike.congr_fun reversal_prefixEmpty_comp
    (T (reversal ((prefixTailEmbedding none).toContinuousLinearMap.adjoint f)))

/-- Exact left-creator defect for every source bounded operator, supported only on the empty outside head. -/
theorem wordSuffixEmbedding_creation_defect (T : WordSpace I →L[ℂ] WordSpace I) (i : I) :
    wordSuffixEmbedding (J := J) T * creation (Sum.inl i) -
      creation (Sum.inl i) * wordSuffixEmbedding T =
    (prefixTailEmbedding none).toContinuousLinearMap.comp
      ((T * creation i - creation i * T).comp
        (prefixTailEmbedding none).toContinuousLinearMap.adjoint) := by
  have h := congrArg wordReversalUnitary.conjStarAlgEquiv
    (prefixOperatorEmbedding_rightCreation_defect (J := J)
      (wordReversalUnitary.conjStarAlgEquiv T) i)
  rw [map_sub, map_mul, map_mul, wordReversalUnitary_conj_rightCreation,
    reversal_prefixEmpty_sandwich, map_sub, map_mul, map_mul,
    wordReversalUnitary_conj_involutive, wordReversalUnitary_conj_rightCreation] at h
  exact h

end FreeProbability.Fock

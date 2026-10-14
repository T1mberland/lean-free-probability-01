import FreeProbability.Fock.SecondQuantizationSuffixDefectReversal

/-! # Literal Γ(V)-supported creator defects on fixed completed tensor Fock spaces -/
noncomputable section
open scoped Classical
namespace FreeProbability.Fock
attribute [local irreducible] fullFockTensorDecomposition isometryPrefixTargetUnitary
  isometrySuffixEmbedding wordSuffixEmbedding
section General
variable {E F G L : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

theorem suffixUnitary_sandwich (U : E ≃ₗᵢ[ℂ] G) (W : F ≃ₗᵢ[ℂ] L)
    (J : E →L[ℂ] F) (V : G →L[ℂ] L)
    (h : W.toLinearIsometry.toContinuousLinearMap.comp J = V.comp U.toLinearIsometry.toContinuousLinearMap)
    (T : E →L[ℂ] E) :
    W.conjStarAlgEquiv (J.comp (T.comp J.adjoint)) =
      V.comp ((U.conjStarAlgEquiv T).comp V.adjoint) := by
  have hW : W.toLinearIsometry.toContinuousLinearMap = (W : F →L[ℂ] L) := by
    apply ContinuousLinearMap.ext; intro f; rfl
  have hU : U.toLinearIsometry.toContinuousLinearMap = (U : E →L[ℂ] G) := by
    apply ContinuousLinearMap.ext; intro f; rfl
  rw [hW, hU] at h
  have ha := congrArg ContinuousLinearMap.adjoint h
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    W.adjoint_eq_symm, U.adjoint_eq_symm] at ha
  apply ContinuousLinearMap.ext
  intro f
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, ContinuousLinearMap.comp_apply]
  have h1 := DFunLike.congr_fun ha f
  change J.adjoint (W.symm f) = U.symm (V.adjoint f) at h1
  rw [h1]
  exact DFunLike.congr_fun h (T (U.symm (V.adjoint f)))
end General

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Exact unitary transport of every empty-tail source sandwich into literal Γ(V) compression. -/
theorem suffixPrefixUnitary_sandwich (V : H →ₗᵢ[ℂ] K)
    (A : FullFock H →L[ℂ] FullFock H) :
    (isometryPrefixTargetUnitary V).conjStarAlgEquiv
      ((prefixTailEmbedding none).toContinuousLinearMap.comp
        (A.comp (prefixTailEmbedding none).toContinuousLinearMap.adjoint)) =
      (secondQuantizationIsometry V).toContinuousLinearMap.comp
        (((fullFockTensorDecomposition H).conjStarAlgEquiv A).comp
          (secondQuantizationIsometry V).toContinuousLinearMap.adjoint) :=
  suffixUnitary_sandwich (fullFockTensorDecomposition H) (isometryPrefixTargetUnitary V)
    (prefixTailEmbedding none).toContinuousLinearMap (secondQuantizationIsometry V).toContinuousLinearMap
    (secondQuantizationIsometry_prefix_comp V).symm A

theorem suffixSourceUnitary_creation_basis (i : fullFockBasisSet H) :
    (fullFockTensorDecomposition H).conjStarAlgEquiv (creation i) = tensorCreation H (fullFockBasis H i) := by
  change tensorOperatorEquiv H (creation i) = tensorOperatorEquiv H
    (basisCreation (fullFockBasis H) (fullFockBasis H i))
  rw [basisCreation_basis]

/-- Unconditional exact creator defect on every source basis vector, for arbitrary bounded T. -/
theorem isometrySuffixEmbedding_creation_defect_basis (V : H →ₗᵢ[ℂ] K)
    (T : TensorFullFock H →L[ℂ] TensorFullFock H) (i : fullFockBasisSet H) :
    isometrySuffixEmbedding V T * tensorCreation K (V (fullFockBasis H i)) -
      tensorCreation K (V (fullFockBasis H i)) * isometrySuffixEmbedding V T =
    (secondQuantizationIsometry V).toContinuousLinearMap.comp
      ((T * tensorCreation H (fullFockBasis H i) - tensorCreation H (fullFockBasis H i) * T).comp
        (secondQuantizationIsometry V).toContinuousLinearMap.adjoint) := by
  have h := congrArg (isometryPrefixTargetUnitary V).conjStarAlgEquiv
    (wordSuffixEmbedding_creation_defect (J := IsometryPrefixOutside V)
      ((fullFockTensorDecomposition H).symm.conjStarAlgEquiv T) i)
  rw [map_sub, map_mul, map_mul, ← isometrySuffixEmbedding_word_transport] at h
  rw [isometryPrefixTargetUnitary_creation V i] at h
  rw [suffixPrefixUnitary_sandwich V] at h
  rw [map_sub, map_mul, map_mul, suffixSourceUnitary_creation_basis (H := H) i] at h
  rw [← LinearIsometryEquiv.symm_conjStarAlgEquiv, StarAlgEquiv.apply_symm_apply] at h
  exact h

end FreeProbability.Fock

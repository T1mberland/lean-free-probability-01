import FreeProbability.Fock.SecondQuantizationSuffixFields

/-! # Exact suffix word/tensor transport and outside basis operator commutation -/
noncomputable section
open scoped Classical
namespace FreeProbability.Fock
attribute [local irreducible] fullFockTensorDecomposition isometryPrefixTargetUnitary

section General
variable {I E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem transportedWordReversal_conj (W : WordSpace I ≃ₗᵢ[ℂ] E)
    (T : WordSpace I →L[ℂ] WordSpace I) :
    (transportedWordReversal W).conjStarAlgEquiv (W.conjStarAlgEquiv T) =
      W.conjStarAlgEquiv (wordReversalUnitary.conjStarAlgEquiv T) := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    transportedWordReversal_apply, transportedWordReversal_symm_apply,
    LinearIsometryEquiv.symm_apply_apply, wordReversalUnitary_apply,
    wordReversalUnitary_symm_apply]

theorem transportedWordReversal_source_conj (W : WordSpace I ≃ₗᵢ[ℂ] E) (T : E →L[ℂ] E) :
    W.symm.conjStarAlgEquiv ((transportedWordReversal W).conjStarAlgEquiv T) =
      wordReversalUnitary.conjStarAlgEquiv (W.symm.conjStarAlgEquiv T) := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    transportedWordReversal_apply, transportedWordReversal_symm_apply,
    LinearIsometryEquiv.symm_apply_apply, wordReversalUnitary_apply,
    wordReversalUnitary_symm_apply, LinearIsometryEquiv.symm_symm]
end General

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The actual all-operator tensor suffix representation is exactly transported word suffix amplification. -/
theorem isometrySuffixEmbedding_word_transport (V : H →ₗᵢ[ℂ] K)
    (T : TensorFullFock H →L[ℂ] TensorFullFock H) :
    isometrySuffixEmbedding V T = (isometryPrefixTargetUnitary V).conjStarAlgEquiv
      (wordSuffixEmbedding ((fullFockTensorDecomposition H).symm.conjStarAlgEquiv T)) := by
  change (transportedWordReversal (isometryPrefixTargetUnitary V)).conjStarAlgEquiv
    ((isometryPrefixTargetUnitary V).conjStarAlgEquiv
      (prefixOperatorEmbedding ((fullFockTensorDecomposition H).symm.conjStarAlgEquiv
        ((transportedWordReversal (fullFockTensorDecomposition H)).conjStarAlgEquiv T)))) = _
  rw [transportedWordReversal_source_conj, transportedWordReversal_conj]
  rfl

/-- Every letter in the adapted split target basis is identified with its literal tensor creator. -/
theorem suffixTargetUnitary_creation_basis (V : H →ₗᵢ[ℂ] K)
    (a : Sum (fullFockBasisSet H) (IsometryPrefixOutside V)) :
    (isometryPrefixTargetUnitary V).conjStarAlgEquiv (creation a) =
      tensorCreation K ((isometryPrefixBasis V).basis (isometryPrefixAlphabet V a)) := by
  unfold isometryPrefixTargetUnitary
  change (isometryPrefixBasis V).tensorOperatorTransport
    ((wordAlphabetUnitary (isometryPrefixAlphabet V)).conjStarAlgEquiv (creation a)) = _
  rw [wordAlphabetUnitary_conj_creation,
    ← basisCreation_basis (isometryPrefixBasis V).basis (isometryPrefixAlphabet V a)]
  exact (isometryPrefixBasis V).tensorOperatorTransport_creation _

/-- ALL source operators' suffix images commute with the actual outside adapted-basis left creators. -/
theorem isometrySuffixEmbedding_commute_creation_outside_basis (V : H →ₗᵢ[ℂ] K)
    (T : TensorFullFock H →L[ℂ] TensorFullFock H) (j : IsometryPrefixOutside V) :
    Commute (isometrySuffixEmbedding V T)
      (tensorCreation K ((isometryPrefixBasis V).basis (isometryPrefixAlphabet V (Sum.inr j)))) := by
  have h := congrArg (isometryPrefixTargetUnitary V).conjStarAlgEquiv
    (wordSuffixEmbedding_commute_creation_outside
      ((fullFockTensorDecomposition H).symm.conjStarAlgEquiv T) j).eq
  rw [map_mul, map_mul, suffixTargetUnitary_creation_basis,
    ← isometrySuffixEmbedding_word_transport] at h
  exact h

/-- The outside adapted-basis annihilator commutes by actual adjoint transport. -/
theorem isometrySuffixEmbedding_commute_annihilation_outside_basis (V : H →ₗᵢ[ℂ] K)
    (T : TensorFullFock H →L[ℂ] TensorFullFock H) (j : IsometryPrefixOutside V) :
    Commute (isometrySuffixEmbedding V T)
      (tensorAnnihilation K ((isometryPrefixBasis V).basis (isometryPrefixAlphabet V (Sum.inr j)))) := by
  have h := congrArg star (isometrySuffixEmbedding_commute_creation_outside_basis V (star T) j).eq
  simp only [star_mul, map_star, star_star] at h
  exact h.symm

theorem suffixSourceTensorUnitary_field_basis (i : fullFockBasisSet H) :
    (fullFockTensorDecomposition H).conjStarAlgEquiv (semicircular i) =
      tensorFamilyField (fullFockBasis H) i := by
  have hc : (fullFockTensorDecomposition H).conjStarAlgEquiv (creation i) =
      tensorCreation H (fullFockBasis H i) := by
    change tensorOperatorEquiv H (creation i) = tensorOperatorEquiv H
      (basisCreation (fullFockBasis H) (fullFockBasis H i))
    rw [basisCreation_basis]
  change (fullFockTensorDecomposition H).conjStarAlgEquiv (creation i + star (creation i)) =
    tensorCreation H (fullFockBasis H i) + star (tensorCreation H (fullFockBasis H i))
  rw [map_add, map_star, hc]

theorem suffixTargetUnitary_field_basis (V : H →ₗᵢ[ℂ] K) (i : fullFockBasisSet H) :
    (isometryPrefixTargetUnitary V).conjStarAlgEquiv (semicircular (Sum.inl i)) =
      tensorFamilyField (fun j => V (fullFockBasis H j)) i := by
  change (isometryPrefixTargetUnitary V).conjStarAlgEquiv
    (creation (Sum.inl i) + star (creation (Sum.inl i))) =
    tensorCreation K (V (fullFockBasis H i)) + star (tensorCreation K (V (fullFockBasis H i)))
  rw [map_add, map_star, isometryPrefixTargetUnitary_creation]

/-- Genuine source-basis field commutant transport into the actual included tensor field commutant. -/
theorem isometrySuffixEmbedding_commute_field_basis (V : H →ₗᵢ[ℂ] K)
    (T : TensorFullFock H →L[ℂ] TensorFullFock H) (i : fullFockBasisSet H)
    (hT : Commute T (tensorFamilyField (fullFockBasis H) i)) :
    Commute (isometrySuffixEmbedding V T) (tensorFamilyField (fun j => V (fullFockBasis H j)) i) := by
  have hs := congrArg (fullFockTensorDecomposition H).symm.conjStarAlgEquiv hT.eq
  rw [map_mul, map_mul, ← suffixSourceTensorUnitary_field_basis] at hs
  rw [← LinearIsometryEquiv.symm_conjStarAlgEquiv, StarAlgEquiv.symm_apply_apply] at hs
  have hw := wordSuffixEmbedding_commute_semicircular (J := IsometryPrefixOutside V)
    ((fullFockTensorDecomposition H).symm.conjStarAlgEquiv T) i hs
  have ht := congrArg (isometryPrefixTargetUnitary V).conjStarAlgEquiv hw.eq
  rw [map_mul, map_mul, ← isometrySuffixEmbedding_word_transport, suffixTargetUnitary_field_basis] at ht
  exact ht

end FreeProbability.Fock

import FreeProbability.Fock.SecondQuantizationPrefixIdentificationNative

/-! # Actual second quantization is the empty-tail prefix sector -/
noncomputable section
open scoped Classical ENNReal
namespace FreeProbability.Fock
theorem identification_prefixTailEmbedding_word {I J : Type*} (t : PrefixTail I J) (w : List I) :
    prefixTailEmbedding t (word w) = word (joinPrefixTail (w, t)) := by
  have hw : word w = lp.single 2 w (1 : ℂ) := by
    apply lp.ext
    funext v
    simp [word, lp.single_apply, Pi.single_apply]
  rw [hw, prefixTailEmbedding_single, one_smul]

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Actual empty-tail sector as an isometry from the full source word model. -/
def isometryPrefixEmptySector (V : H →ₗᵢ[ℂ] K) : FullFock H →ₗᵢ[ℂ] TensorFullFock K :=
  (isometryPrefixTargetUnitary V).toLinearIsometry.comp (prefixTailEmbedding none)

theorem isometryPrefixEmptySector_vacuum (V : H →ₗᵢ[ℂ] K) :
    isometryPrefixEmptySector V (fullVacuum H) = tensorVacuum K := by
  have hh : prefixTailEmbedding (J := IsometryPrefixOutside V) none (fullVacuum H) = word [] :=
    identification_prefixTailEmbedding_word none []
  change isometryPrefixTargetUnitary V (prefixTailEmbedding none (fullVacuum H)) = _
  rw [hh]
  change (isometryPrefixBasis V).tensorTransport
    (wordAlphabetUnitary (isometryPrefixAlphabet V) (word [])) = _
  rw [wordAlphabetUnitary_word]
  exact (isometryPrefixBasis V).tensorTransport_vacuum

/-- Exact included basis creation on the complete empty-tail sector. -/
theorem isometryPrefixEmptySector_creation (V : H →ₗᵢ[ℂ] K) (i : fullFockBasisSet H) (f : FullFock H) :
    isometryPrefixEmptySector V (creation i f) =
      tensorCreation K (V (fullFockBasis H i)) (isometryPrefixEmptySector V f) := by
  have hp := DFunLike.congr_fun (prefixTailEmbedding_creation_comp
    (J := IsometryPrefixOutside V) none i) f
  change prefixTailEmbedding none (creation i f) =
    creation (Sum.inl i) (prefixTailEmbedding none f) at hp
  have hc := DFunLike.congr_fun (isometryPrefixTargetUnitary_creation V i)
    (isometryPrefixTargetUnitary V (prefixTailEmbedding none f))
  change isometryPrefixTargetUnitary V (creation (Sum.inl i)
    ((isometryPrefixTargetUnitary V).symm
      (isometryPrefixTargetUnitary V (prefixTailEmbedding none f)))) = _ at hc
  rw [LinearIsometryEquiv.symm_apply_apply] at hc
  exact (congrArg (isometryPrefixTargetUnitary V) hp).trans hc

/-- Literal second quantization and the actual empty-tail sector agree on every source basis word. -/
theorem secondQuantizationIsometry_prefix_word (V : H →ₗᵢ[ℂ] K) (w : List (fullFockBasisSet H)) :
    secondQuantizationIsometry V (fullFockTensorDecomposition H (word w)) =
      isometryPrefixEmptySector V (word w) := by
  induction w with
  | nil =>
    change secondQuantizationIsometry V (fullFockTensorDecomposition H (fullVacuum H)) =
      isometryPrefixEmptySector V (fullVacuum H)
    have hs : fullFockTensorDecomposition H (fullVacuum H) = tensorVacuum H :=
      fullFockTensorDecomposition_vacuum H
    rw [hs, secondQuantizationIsometry_vacuum, isometryPrefixEmptySector_vacuum]
  | cons i w hw =>
    have hs : fullFockTensorDecomposition H (word (i :: w)) =
        tensorCreation H (fullFockBasis H i) (fullFockTensorDecomposition H (word w)) := by
      rw [tensorCreation_apply, LinearIsometryEquiv.symm_apply_apply]
      change fullFockTensorDecomposition H (word (i :: w)) =
        fullFockTensorDecomposition H (basisCreation (fullFockBasis H) (fullFockBasis H i) (word w))
      rw [basisCreation_basis, creation_word]
    have hi := DFunLike.congr_fun (secondQuantizationIsometry_creation_comp V (fullFockBasis H i))
      (fullFockTensorDecomposition H (word w))
    change secondQuantizationIsometry V
      (tensorCreation H (fullFockBasis H i) (fullFockTensorDecomposition H (word w))) =
      tensorCreation K (V (fullFockBasis H i))
        (secondQuantizationIsometry V (fullFockTensorDecomposition H (word w))) at hi
    rw [hs, hi, hw, ← creation_word, isometryPrefixEmptySector_creation]

/-- Equality on the entire COMPLETE source Hilbert space, not just finite tensors. -/
theorem secondQuantizationIsometry_prefix_comp (V : H →ₗᵢ[ℂ] K) :
    (secondQuantizationIsometry V).toContinuousLinearMap.comp
      (fullFockTensorDecomposition H).toLinearIsometry.toContinuousLinearMap =
        (isometryPrefixEmptySector V).toContinuousLinearMap := by
  apply lp.ext_continuousLinearMap (ENNReal.ofNat_ne_top (n := 2))
  intro w
  apply ContinuousLinearMap.ext
  intro c
  have hs : lp.single 2 w c = c • word w := by
    apply lp.ext
    funext v
    simp [word, lp.single_apply, Pi.single_apply]
  change secondQuantizationIsometry V (fullFockTensorDecomposition H (lp.single 2 w c)) =
    isometryPrefixEmptySector V (lp.single 2 w c)
  rw [hs, map_smul, map_smul, map_smul, secondQuantizationIsometry_prefix_word]

/-- Γ(V) is literally the empty-tail sector on every infinite tensor Fock vector. -/
theorem secondQuantizationIsometry_prefix_sector (V : H →ₗᵢ[ℂ] K) (f : TensorFullFock H) :
    secondQuantizationIsometry V f = isometryPrefixTargetUnitary V
      (prefixTailEmbedding none ((fullFockTensorDecomposition H).symm f)) := by
  have h := DFunLike.congr_fun (secondQuantizationIsometry_prefix_comp V)
    ((fullFockTensorDecomposition H).symm f)
  change secondQuantizationIsometry V
    (fullFockTensorDecomposition H ((fullFockTensorDecomposition H).symm f)) = _ at h
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  exact h

end FreeProbability.Fock

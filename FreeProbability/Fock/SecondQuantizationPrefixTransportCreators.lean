import FreeProbability.Fock.SecondQuantizationPrefixTransport
import Mathlib.Analysis.CStarAlgebra.Hom

/-! # Exact creator transport in the arbitrary-isometry prefix representation -/
noncomputable section
open scoped Classical ENNReal
namespace FreeProbability.Fock
variable {I J : Type*}

theorem wordAlphabetUnitary_creation_comp (e : I ≃ J) (i : I) :
    (wordAlphabetUnitary e).toLinearIsometry.toContinuousLinearMap.comp (creation i) =
      (creation (e i)).comp (wordAlphabetUnitary e).toLinearIsometry.toContinuousLinearMap := by
  apply lp.ext_continuousLinearMap (ENNReal.ofNat_ne_top (n := 2))
  intro w
  apply ContinuousLinearMap.ext
  intro c
  change wordAlphabetUnitary e (creation i (lp.single 2 w c)) =
    creation (e i) (wordAlphabetUnitary e (lp.single 2 w c))
  have hw : lp.single 2 w c = c • word w := by
    apply lp.ext
    funext v
    simp [word, lp.single_apply, Pi.single_apply]
  rw [hw, map_smul, creation_word, map_smul, wordAlphabetUnitary_word]
  rw [map_smul, wordAlphabetUnitary_word, map_smul, creation_word]
  rfl

theorem wordAlphabetUnitary_conj_creation (e : I ≃ J) (i : I) :
    (wordAlphabetUnitary e).conjStarAlgEquiv (creation i) = creation (e i) := by
  apply ContinuousLinearMap.ext
  intro f
  change wordAlphabetUnitary e (creation i ((wordAlphabetUnitary e).symm f)) = _
  have h := DFunLike.congr_fun (wordAlphabetUnitary_creation_comp e i) ((wordAlphabetUnitary e).symm f)
  change wordAlphabetUnitary e (creation i ((wordAlphabetUnitary e).symm f)) =
    creation (e i) (wordAlphabetUnitary e ((wordAlphabetUnitary e).symm f)) at h
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  exact h

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Exact included basis creator identification in the fixed target completed tensor Fock space. -/
theorem isometryPrefixTargetUnitary_creation (V : H →ₗᵢ[ℂ] K) (i : fullFockBasisSet H) :
    (isometryPrefixTargetUnitary V).conjStarAlgEquiv (creation (Sum.inl i)) =
      tensorCreation K (V (fullFockBasis H i)) := by
  change (isometryPrefixBasis V).tensorOperatorTransport
    ((wordAlphabetUnitary (isometryPrefixAlphabet V)).conjStarAlgEquiv (creation (Sum.inl i))) = _
  rw [wordAlphabetUnitary_conj_creation, isometryPrefixAlphabet_inl,
    ← (isometryPrefixBasis V).creation_family i,
    (isometryPrefixBasis V).tensorOperatorTransport_creation]

/-- The actual arbitrary-isometry embedding sends every source basis creator to its included creator. -/
theorem isometryPrefixEmbedding_creation_basis (V : H →ₗᵢ[ℂ] K) (i : fullFockBasisSet H) :
    isometryPrefixEmbedding V (tensorCreation H (fullFockBasis H i)) =
      tensorCreation K (V (fullFockBasis H i)) := by
  have hs : (fullFockTensorDecomposition H).symm.conjStarAlgEquiv
      (tensorCreation H (fullFockBasis H i)) = creation i := by
    change (tensorOperatorEquiv H).symm
      (tensorOperatorEquiv H (fullCreation H (fullFockBasis H i))) = _
    rw [StarAlgEquiv.symm_apply_apply]
    exact basisCreation_basis (fullFockBasis H) i
  change (isometryPrefixTargetUnitary V).conjStarAlgEquiv
    (prefixOperatorEmbedding ((fullFockTensorDecomposition H).symm.conjStarAlgEquiv
      (tensorCreation H (fullFockBasis H i)))) = _
  rw [hs, prefixOperatorEmbedding_creation, isometryPrefixTargetUnitary_creation]

/-- Actual continuous complex-linear creator map on the fixed tensor Fock space. -/
def prefixTensorCreationContinuous (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] :
    H →L[ℂ] (TensorFullFock H →L[ℂ] TensorFullFock H) :=
  ((tensorOperatorEquiv H).toAlgEquiv.toLinearEquiv.toLinearMap.comp
    (basisCreationIsometry (fullFockBasis H)).toLinearMap).mkContinuous 1 (by
      intro h
      change ‖tensorCreation H h‖ ≤ 1 * ‖h‖
      rw [norm_tensorCreation, one_mul])

/-- Actual all-operator embedding as a norm-continuous linear map. -/
def isometryPrefixEmbeddingContinuous (V : H →ₗᵢ[ℂ] K) :
    (TensorFullFock H →L[ℂ] TensorFullFock H) →L[ℂ]
      (TensorFullFock K →L[ℂ] TensorFullFock K) :=
  (isometryPrefixEmbedding V).toAlgHom.toLinearMap.mkContinuous 1 (by
    intro T
    change ‖isometryPrefixEmbedding V T‖ ≤ 1 * ‖T‖
    rw [NonUnitalStarAlgHom.norm_map (isometryPrefixEmbedding V) (isometryPrefixEmbedding_injective V),
      one_mul])

/-- Exact arbitrary-vector creator transport, with no spanning/countability assumptions. -/
theorem isometryPrefixEmbedding_creation (V : H →ₗᵢ[ℂ] K) (h : H) :
    isometryPrefixEmbedding V (tensorCreation H h) = tensorCreation K (V h) := by
  let F := (isometryPrefixEmbeddingContinuous V).comp (prefixTensorCreationContinuous H)
  let G := (prefixTensorCreationContinuous K).comp V.toContinuousLinearMap
  have hs := F.hasSum ((fullFockBasis H).hasSum_repr h)
  have ht := G.hasSum ((fullFockBasis H).hasSum_repr h)
  have heq (i : fullFockBasisSet H) :
      F ((fullFockBasis H).repr h i • fullFockBasis H i) =
        G ((fullFockBasis H).repr h i • fullFockBasis H i) := by
    rw [map_smul, map_smul]
    apply congrArg ((fullFockBasis H).repr h i • ·)
    exact isometryPrefixEmbedding_creation_basis V i
  simp only [heq] at hs
  exact hs.unique ht

/-- True adjoint transport for every one-particle vector. -/
theorem isometryPrefixEmbedding_annihilation (V : H →ₗᵢ[ℂ] K) (h : H) :
    isometryPrefixEmbedding V (tensorAnnihilation H h) = tensorAnnihilation K (V h) := by
  change isometryPrefixEmbedding V (star (tensorCreation H h)) = star (tensorCreation K (V h))
  rw [map_star, isometryPrefixEmbedding_creation]

end FreeProbability.Fock

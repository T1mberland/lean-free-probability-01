import FreeProbability.Fock.SecondQuantizationSuffixDefectFields
import FreeProbability.Fock.SecondQuantizationPrefixVonNeumann

/-! # Actual suffix intertwining transfers commutation through full Γ-compression -/
noncomputable section
open scoped Classical
namespace FreeProbability.Fock
attribute [local irreducible] fullFockTensorDecomposition isometryPrefixTargetUnitary
  isometrySuffixEmbedding wordSuffixEmbedding
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The actual adjoint inclusion intertwines every suffix-represented bounded operator. -/
theorem suffixEmbedding_adjoint_inclusion (V : H →ₗᵢ[ℂ] K)
    (B : TensorFullFock H →L[ℂ] TensorFullFock H) :
    (secondQuantizationIsometry V).toContinuousLinearMap.adjoint.comp (isometrySuffixEmbedding V B) =
      B.comp (secondQuantizationIsometry V).toContinuousLinearMap.adjoint := by
  have h := congrArg ContinuousLinearMap.adjoint (isometrySuffixEmbedding_inclusion_comp V (star B))
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp] at h
  have hΦ : (isometrySuffixEmbedding V (star B)).adjoint = isometrySuffixEmbedding V B := by
    change star (isometrySuffixEmbedding V (star B)) = _
    rw [map_star, star_star]
  have hB : (star B).adjoint = B := by
    change B.adjoint.adjoint = B
    exact ContinuousLinearMap.adjoint_adjoint B
  rw [hΦ, hB] at h
  exact h

/-- Actual ambient compression commutes with B whenever the input commutes with its actual suffix image. -/
theorem suffixEmbedding_compression_commute (V : H →ₗᵢ[ℂ] K)
    (A : TensorFullFock K →L[ℂ] TensorFullFock K)
    (B : TensorFullFock H →L[ℂ] TensorFullFock H)
    (hA : Commute A (isometrySuffixEmbedding V B)) :
    Commute (secondQuantizationCompression V A) B := by
  apply ContinuousLinearMap.ext
  intro f
  change (secondQuantizationIsometry V).toContinuousLinearMap.adjoint
    (A (secondQuantizationIsometry V (B f))) =
      B ((secondQuantizationIsometry V).toContinuousLinearMap.adjoint
        (A (secondQuantizationIsometry V f)))
  have h1 := isometrySuffixEmbedding_inclusion V B f
  have h2 := DFunLike.congr_fun hA.eq (secondQuantizationIsometry V f)
  change A (isometrySuffixEmbedding V B (secondQuantizationIsometry V f)) =
    isometrySuffixEmbedding V B (A (secondQuantizationIsometry V f)) at h2
  have h3 := DFunLike.congr_fun (suffixEmbedding_adjoint_inclusion V B)
    (A (secondQuantizationIsometry V f))
  calc
    _ = (secondQuantizationIsometry V).toContinuousLinearMap.adjoint
        (A (isometrySuffixEmbedding V B (secondQuantizationIsometry V f))) :=
      congrArg (fun x => (secondQuantizationIsometry V).toContinuousLinearMap.adjoint (A x)) h1.symm
    _ = (secondQuantizationIsometry V).toContinuousLinearMap.adjoint
        (isometrySuffixEmbedding V B (A (secondQuantizationIsometry V f))) :=
      congrArg (secondQuantizationIsometry V).toContinuousLinearMap.adjoint h2
    _ = _ := h3

end FreeProbability.Fock

import FreeProbability.Fock.SecondQuantizationSuffixDefectTensor

/-! # Exact unconditional suffix creator defect for EVERY complex one-particle vector -/
noncomputable section
open scoped Classical
namespace FreeProbability.Fock
attribute [local irreducible] fullFockTensorDecomposition isometryPrefixTargetUnitary
  isometrySuffixEmbedding wordSuffixEmbedding
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Actual bounded Γ(V)-sandwich as a continuous complex-linear map between full operator spaces. -/
def suffixSandwichContinuous (V : H →ₗᵢ[ℂ] K) :
    (TensorFullFock H →L[ℂ] TensorFullFock H) →L[ℂ]
      (TensorFullFock K →L[ℂ] TensorFullFock K) :=
  ((ContinuousLinearMap.compL ℂ (TensorFullFock K) (TensorFullFock H) (TensorFullFock K)).flip
    (secondQuantizationIsometry V).toContinuousLinearMap.adjoint).comp
      (ContinuousLinearMap.compL ℂ (TensorFullFock H) (TensorFullFock H) (TensorFullFock K)
        (secondQuantizationIsometry V).toContinuousLinearMap)

@[simp] theorem suffixSandwichContinuous_apply (V : H →ₗᵢ[ℂ] K)
    (T : TensorFullFock H →L[ℂ] TensorFullFock H) :
    suffixSandwichContinuous V T = (secondQuantizationIsometry V).toContinuousLinearMap.comp
      (T.comp (secondQuantizationIsometry V).toContinuousLinearMap.adjoint) := rfl

/-- No source commutation hypothesis: creator commutator is exactly Γ(V) times the source defect times Γ(V)†. -/
theorem isometrySuffixEmbedding_creation_defect (V : H →ₗᵢ[ℂ] K)
    (T : TensorFullFock H →L[ℂ] TensorFullFock H) (h : H) :
    isometrySuffixEmbedding V T * tensorCreation K (V h) -
      tensorCreation K (V h) * isometrySuffixEmbedding V T =
    (secondQuantizationIsometry V).toContinuousLinearMap.comp
      ((T * tensorCreation H h - tensorCreation H h * T).comp
        (secondQuantizationIsometry V).toContinuousLinearMap.adjoint) := by
  let S := isometrySuffixEmbedding V T
  let F := ((ContinuousLinearMap.mul ℂ (TensorFullFock K →L[ℂ] TensorFullFock K) S) -
    (ContinuousLinearMap.mul ℂ (TensorFullFock K →L[ℂ] TensorFullFock K)).flip S).comp
      ((prefixTensorCreationContinuous K).comp V.toContinuousLinearMap)
  let G := (suffixSandwichContinuous V).comp
    (((ContinuousLinearMap.mul ℂ (TensorFullFock H →L[ℂ] TensorFullFock H) T) -
      (ContinuousLinearMap.mul ℂ (TensorFullFock H →L[ℂ] TensorFullFock H)).flip T).comp
        (prefixTensorCreationContinuous H))
  have hs := F.hasSum ((fullFockBasis H).hasSum_repr h)
  have ht := G.hasSum ((fullFockBasis H).hasSum_repr h)
  have heq (i : fullFockBasisSet H) :
      F ((fullFockBasis H).repr h i • fullFockBasis H i) =
        G ((fullFockBasis H).repr h i • fullFockBasis H i) := by
    rw [map_smul, map_smul]
    apply congrArg ((fullFockBasis H).repr h i • ·)
    exact isometrySuffixEmbedding_creation_defect_basis V T i
  simp only [heq] at hs
  exact hs.unique ht

/-- Actual Hilbert adjoint commutes with the literal Γ(V)-sandwich. -/
theorem suffixSandwichContinuous_star (V : H →ₗᵢ[ℂ] K)
    (T : TensorFullFock H →L[ℂ] TensorFullFock H) :
    star (suffixSandwichContinuous V T) = suffixSandwichContinuous V (star T) := by
  change ((secondQuantizationIsometry V).toContinuousLinearMap.comp
    (T.comp (secondQuantizationIsometry V).toContinuousLinearMap.adjoint)).adjoint = _
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_assoc]
  rfl

end FreeProbability.Fock

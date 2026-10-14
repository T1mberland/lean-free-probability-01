import FreeProbability.Fock.SecondQuantizationPrefixReindex
import FreeProbability.Fock.SecondQuantizationPrefixBoundedWOT
import FreeProbability.Fock.TensorFamilyFaithfulnessEquiv

/-! # Actual arbitrary-isometry prefix embedding on fixed completed tensor Fock spaces

Construction of the full-space representation. Exact arbitrary-vector creator
identification and bounded-WOT transport are separate subsequent theorems.
-/
noncomputable section
open scoped Classical
namespace FreeProbability.Fock
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Extend the included full source Hilbert basis to a full target Hilbert basis. -/
def isometryPrefixBasis (V : H →ₗᵢ[ℂ] K) :
    OrthonormalFamilyExtension (fun i : fullFockBasisSet H => V (fullFockBasis H i)) :=
  orthonormalFamilyExtension ((fullFockBasis H).orthonormal.comp_linearIsometry V)

/-- Target basis letters outside the included full source basis range. -/
abbrev IsometryPrefixOutside (V : H →ₗᵢ[ℂ] K) :=
  {j : (isometryPrefixBasis V).indices // j ∉ Set.range (isometryPrefixBasis V).index}

/-- The genuine target alphabet splits into the included source alphabet and its complement. -/
def isometryPrefixAlphabet (V : H →ₗᵢ[ℂ] K) :
    Sum (fullFockBasisSet H) (IsometryPrefixOutside V) ≃ (isometryPrefixBasis V).indices :=
  (Equiv.sumCongr (Equiv.ofInjective (isometryPrefixBasis V).index
    (isometryPrefixBasis V).index_injective) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range (isometryPrefixBasis V).index))

@[simp] theorem isometryPrefixAlphabet_inl (V : H →ₗᵢ[ℂ] K) (i : fullFockBasisSet H) :
    isometryPrefixAlphabet V (Sum.inl i) = (isometryPrefixBasis V).index i := rfl

/-- Actual whole-space unitary from the split target word model to fixed literal tensor Fock K. -/
def isometryPrefixTargetUnitary (V : H →ₗᵢ[ℂ] K) :
    WordSpace (Sum (fullFockBasisSet H) (IsometryPrefixOutside V)) ≃ₗᵢ[ℂ] TensorFullFock K :=
  (wordAlphabetUnitary (isometryPrefixAlphabet V)).trans (isometryPrefixBasis V).tensorTransport

/-- True unital bounded-operator embedding between fixed tensor Fock spaces for ANY isometry. -/
def isometryPrefixEmbedding (V : H →ₗᵢ[ℂ] K) :
    (TensorFullFock H →L[ℂ] TensorFullFock H) →⋆ₐ[ℂ]
      (TensorFullFock K →L[ℂ] TensorFullFock K) :=
  (isometryPrefixTargetUnitary V).conjStarAlgEquiv.toStarAlgHom.comp
    (prefixOperatorEmbedding.comp (fullFockTensorDecomposition H).symm.conjStarAlgEquiv.toStarAlgHom)

theorem isometryPrefixEmbedding_injective (V : H →ₗᵢ[ℂ] K) :
    Function.Injective (isometryPrefixEmbedding V) :=
  (isometryPrefixTargetUnitary V).conjStarAlgEquiv.injective.comp
    (prefixOperatorEmbedding_injective.comp
      (fullFockTensorDecomposition H).symm.conjStarAlgEquiv.injective)

end FreeProbability.Fock

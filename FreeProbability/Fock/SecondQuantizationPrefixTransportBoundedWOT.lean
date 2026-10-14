import FreeProbability.Fock.SecondQuantizationPrefixTransportCreators

/-! # Actual arbitrary-isometry embedding preserves bounded-WOT convergence

The topology is induced WOT on each source norm ball. No global continuity on
unbounded operator nets, inverse closure surjectivity, or normal OU claim occurs.
-/
noncomputable section
open scoped Classical NNReal
namespace FreeProbability.Fock
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Actual unitary conjugation preserves each operator norm ball. -/
def unitaryConjugationWOTNormBall (U : E ≃ₗᵢ[ℂ] F) (C : ℝ≥0) :
    WOTNormBall E C → WOTNormBall F C := fun T =>
  ⟨unitaryConjugationWOT U T.val, by
    change ‖U.conjStarAlgEquiv T.val.toCLM‖ ≤ C
    rw [NonUnitalStarAlgHom.norm_map U.conjStarAlgEquiv U.conjStarAlgEquiv.injective]
    exact T.property⟩

theorem unitaryConjugationWOTNormBall_continuous (U : E ≃ₗᵢ[ℂ] F) (C : ℝ≥0) :
    Continuous (unitaryConjugationWOTNormBall U C) :=
  ((unitaryConjugationWOT_continuous U).comp continuous_subtype_val).subtype_mk _

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Actual transported prefix map on a source norm ball. -/
def prefixUnitaryWOTMap {I J : Type*} (U : E ≃ₗᵢ[ℂ] WordSpace I)
    (W : WordSpace (Sum I J) ≃ₗᵢ[ℂ] F) (C : ℝ≥0) : WOTNormBall E C → (F →WOT[ℂ] F) :=
  (unitaryConjugationWOT W) ∘
    (fun T : WOTNormBall (WordSpace I) C =>
      ContinuousLinearMapWOT.ofCLM (prefixOperatorEmbedding (J := J) T.val.toCLM)) ∘
    unitaryConjugationWOTNormBall U C

/-- Generic unitary transport of prefix amplification on each source norm ball. -/
theorem prefixUnitaryTransport_boundedWOT_continuous {I J : Type*}
    (U : E ≃ₗᵢ[ℂ] WordSpace I)
    (W : WordSpace (Sum I J) ≃ₗᵢ[ℂ] F) (C : ℝ≥0) :
    Continuous (prefixUnitaryWOTMap U W C) := by
  have hU : Continuous (unitaryConjugationWOTNormBall U C) :=
    unitaryConjugationWOTNormBall_continuous U C
  have hP : Continuous (fun T : WOTNormBall (WordSpace I) C =>
      ContinuousLinearMapWOT.ofCLM (prefixOperatorEmbedding (J := J) T.val.toCLM)) :=
    prefixOperatorEmbedding_boundedWOT_continuous C
  have hW : Continuous (unitaryConjugationWOT W) := unitaryConjugationWOT_continuous W
  exact hW.comp (hP.comp hU)

/-- Every arbitrary-isometry tensor-Fock embedding is genuinely WOT continuous on each norm ball. -/
theorem isometryPrefixEmbedding_boundedWOT_continuous (V : H →ₗᵢ[ℂ] K) (C : ℝ≥0) :
    Continuous (fun T : WOTNormBall (TensorFullFock H) C =>
      ContinuousLinearMapWOT.ofCLM (isometryPrefixEmbedding V T.val.toCLM)) := by
  have heq : (fun T : WOTNormBall (TensorFullFock H) C =>
      ContinuousLinearMapWOT.ofCLM (isometryPrefixEmbedding V T.val.toCLM)) =
      prefixUnitaryWOTMap (fullFockTensorDecomposition H).symm (isometryPrefixTargetUnitary V) C := by
    funext T
    rfl
  rw [heq]
  exact prefixUnitaryTransport_boundedWOT_continuous
    (fullFockTensorDecomposition H).symm (isometryPrefixTargetUnitary V) C

/-- Actual included real fields, for arbitrary vectors and arbitrary prescribed families. -/
theorem isometryPrefixEmbedding_field {I : Type*} (V : H →ₗᵢ[ℂ] K) (e : I → H) (i : I) :
    isometryPrefixEmbedding V (tensorFamilyField e i) = tensorFamilyField (fun j => V (e j)) i := by
  change isometryPrefixEmbedding V (tensorCreation H (e i) + tensorAnnihilation H (e i)) = _
  rw [map_add, isometryPrefixEmbedding_creation, isometryPrefixEmbedding_annihilation]
  rfl

end FreeProbability.Fock

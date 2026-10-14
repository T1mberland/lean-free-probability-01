import FreeProbability.Fock.OrnsteinUhlenbeckVonNeumannRangeTime

/-! # Correct bounded-WOT continuity of the actual all-operator OU dilation

No global WOT continuity on unbounded nets or positive-supremum normality is
asserted. The source norm-ball topology is the genuine induced WOT topology.
-/
noncomputable section
open scoped Classical NNReal
namespace FreeProbability.Fock
attribute [local irreducible] fullFockTensorDecomposition isometryPrefixTargetUnitary
  isometrySuffixEmbedding wordSuffixEmbedding doubledRotation secondQuantization isometryPrefixEmbedding
  doubledFockRotation doubledFirst doubledSecond fullFockBasis tensorCreation tensorAnnihilation tensorFamilyField
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Actual isometric prefix embedding preserves the source operator norm ball. -/
def prefixEmbeddingWOTNormBall (V : H →ₗᵢ[ℂ] K) (C : ℝ≥0) :
    WOTNormBall (TensorFullFock H) C → WOTNormBall (TensorFullFock K) C := fun T =>
  ⟨ContinuousLinearMapWOT.ofCLM (isometryPrefixEmbedding V T.val.toCLM), by
    change ‖isometryPrefixEmbedding V T.val.toCLM‖ ≤ C
    rw [NonUnitalStarAlgHom.norm_map _ (isometryPrefixEmbedding_injective V)]
    exact T.property⟩

theorem prefixEmbeddingWOTNormBall_continuous (V : H →ₗᵢ[ℂ] K) (C : ℝ≥0) :
    Continuous (prefixEmbeddingWOTNormBall V C) :=
  (isometryPrefixEmbedding_boundedWOT_continuous V C).subtype_mk _

/-- Literal actual OU map in WOT coordinates, restricted to one source norm ball. -/
def ouRangeWOTMap (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1) (C : ℝ≥0) :
    WOTNormBall (TensorFullFock H) C → (TensorFullFock H →WOT[ℂ] TensorFullFock H) :=
  (secondQuantizationCompressionWOT (doubledFirst H)) ∘
    unitaryConjugationWOT (doubledFockRotation H r s hrs) ∘
      (fun T : WOTNormBall (TensorFullFock H) C =>
        ContinuousLinearMapWOT.ofCLM (isometryPrefixEmbedding (doubledFirst H) T.val.toCLM))

theorem ouRangeWOTMap_continuous (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1) (C : ℝ≥0) :
    Continuous (ouRangeWOTMap (H := H) r s hrs C) := by
  have hP : Continuous (fun T : WOTNormBall (TensorFullFock H) C =>
      ContinuousLinearMapWOT.ofCLM (isometryPrefixEmbedding (doubledFirst H) T.val.toCLM)) :=
    isometryPrefixEmbedding_boundedWOT_continuous _ C
  have hR : Continuous (unitaryConjugationWOT (doubledFockRotation H r s hrs)) :=
    unitaryConjugationWOT_continuous _
  have hC : Continuous (secondQuantizationCompressionWOT (doubledFirst H)) :=
    secondQuantizationCompressionWOT_continuous _
  exact hC.comp (hR.comp hP)

/-- Actual all-matrix CP OU map is WOT continuous on EVERY source operator norm ball. -/
theorem ouDoubleCommutantRawCP_boundedWOT_continuous (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1)
    (C : ℝ≥0) :
    Continuous (fun T : WOTNormBall (TensorFullFock H) C =>
      ContinuousLinearMapWOT.ofCLM (ouDoubleCommutantRawCP r s hrs T.val.toCLM)) := by
  have he : (fun T : WOTNormBall (TensorFullFock H) C =>
      ContinuousLinearMapWOT.ofCLM (ouDoubleCommutantRawCP r s hrs T.val.toCLM)) =
      ouRangeWOTMap r s hrs C := by funext T; rfl
  rw [he]
  exact ouRangeWOTMap_continuous r s hrs C

theorem ouDoubleCommutantTimeCP_boundedWOT_continuous (t : ℝ) (ht : 0 ≤ t) (C : ℝ≥0) :
    Continuous (fun T : WOTNormBall (TensorFullFock H) C =>
      ContinuousLinearMapWOT.ofCLM (ouDoubleCommutantTimeCP t ht T.val.toCLM)) :=
  ouDoubleCommutantRawCP_boundedWOT_continuous _ _ _ C

end FreeProbability.Fock

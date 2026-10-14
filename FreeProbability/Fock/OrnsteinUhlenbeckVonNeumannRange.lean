import FreeProbability.Fock.OrnsteinUhlenbeckVonNeumannRangeFields

/-! # Actual OU compression preserves the literal double commutant of ANY prescribed field family

This is a concrete range theorem. No WOT-closure equivalence, Kaplansky density,
semigroup law or normality assertion is required or claimed.
-/
noncomputable section
open scoped Classical
namespace FreeProbability.Fock
attribute [local irreducible] fullFockTensorDecomposition isometryPrefixTargetUnitary
  isometrySuffixEmbedding wordSuffixEmbedding doubledRotation secondQuantization isometryPrefixEmbedding
  doubledFockRotation doubledFirst doubledSecond fullFockBasis tensorCreation tensorAnnihilation tensorFamilyField
variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Generic unitary transport of a prescribed family literal double commutant. -/
theorem ouRange_unitary_mem_familyDoubleCentralizer {I K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (U : K ≃ₗᵢ[ℂ] K) (e : I → K) {T : TensorFullFock K →L[ℂ] TensorFullFock K}
    (hT : T ∈ Set.centralizer (Set.centralizer (Set.range (tensorFamilyField e)))) :
    (secondQuantization U).conjStarAlgEquiv T ∈
      Set.centralizer (Set.centralizer (Set.range (tensorFamilyField (fun j => U (e j))))) := by
  have hr := mulEquiv_mem_doubleCentralizer (secondQuantization U).conjStarAlgEquiv.toMulEquiv
    (Set.range (tensorFamilyField e)) hT
  have he : (secondQuantization U).conjStarAlgEquiv.toMulEquiv '' Set.range (tensorFamilyField e) =
      Set.range (tensorFamilyField (fun j => U (e j))) := by
    rw [← Set.range_comp']
    congr 1
    funext i
    unfold tensorFamilyField
    exact secondQuantization_conj_field U (e i)
  rw [he] at hr
  exact hr

/-- Literal double-commutant membership transports through the actual doubled rotation. -/
theorem ouRange_rotatedIncluded_mem_doubleCentralizer (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1)
    (e : I → H) {T : TensorFullFock H →L[ℂ] TensorFullFock H}
    (hT : T ∈ Set.centralizer (Set.centralizer (Set.range (tensorFamilyField e)))) :
    (doubledFockRotation H r s hrs).conjStarAlgEquiv
      (isometryPrefixEmbedding (doubledFirst H) T) ∈
        Set.centralizer (Set.centralizer (Set.range
          (tensorFamilyField (fun j => doubledRotation r s hrs (doubledFirst H (e j)))))) := by
  have hi := isometryPrefixEmbedding_mem_familyDoubleCentralizer (doubledFirst H) e hT
  unfold doubledFockRotation
  exact ouRange_unitary_mem_familyDoubleCentralizer (doubledRotation r s hrs)
    (fun j => doubledFirst H (e j)) hi

/-- The actual ambient compression of a rotated-family double-commutant operator belongs to the ORIGINAL family double commutant. -/
theorem ouRange_compression_mem_source_doubleCentralizer (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1)
    (e : I → H)
    {A : TensorFullFock (DoubledHilbert H) →L[ℂ] TensorFullFock (DoubledHilbert H)}
    (hA : A ∈ Set.centralizer (Set.centralizer (Set.range
      (tensorFamilyField (fun j => doubledRotation r s hrs (doubledFirst H (e j))))))) :
    secondQuantizationCompression (doubledFirst H) A ∈
      Set.centralizer (Set.centralizer (Set.range (tensorFamilyField e))) := by
  intro B hB
  have hs : isometrySuffixEmbedding (doubledFirst H) B ∈ Set.centralizer (Set.range
      (tensorFamilyField (fun j => doubledRotation r s hrs (doubledFirst H (e j))))) := by
    rintro _ ⟨i, rfl⟩
    have hi : Commute B (tensorFamilyField e i) := (hB _ ⟨i, rfl⟩).symm
    exact (suffixFirst_commute_rotated_field r s hrs e B i hi).eq.symm
  have hc : Commute A (isometrySuffixEmbedding (doubledFirst H) B) := (hA _ hs).symm
  exact (suffixEmbedding_compression_commute (doubledFirst H) A B hc).eq.symm

/-- Literal all-operator rotation-dilation linear map, to be restricted using the proved range. -/
def ouDoubleCommutantRaw (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1) :
    (TensorFullFock H →L[ℂ] TensorFullFock H) →ₗ[ℂ]
      (TensorFullFock H →L[ℂ] TensorFullFock H) :=
  (rotatedFockCompression H r s hrs).toLinearMap.comp
    (isometryPrefixEmbedding (doubledFirst H)).toAlgHom.toLinearMap

/-- Genuine actual OU dilation range on ANY prescribed field family, with no ON or spanning assumptions. -/
theorem ouDoubleCommutantRaw_mem_familyDoubleCentralizer (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1)
    (e : I → H) {T : TensorFullFock H →L[ℂ] TensorFullFock H}
    (hT : T ∈ Set.centralizer (Set.centralizer (Set.range (tensorFamilyField e)))) :
    ouDoubleCommutantRaw r s hrs T ∈ Set.centralizer (Set.centralizer (Set.range (tensorFamilyField e))) := by
  change secondQuantizationCompression (doubledFirst H)
    ((doubledFockRotation H r s hrs).conjStarAlgEquiv (isometryPrefixEmbedding (doubledFirst H) T)) ∈ _
  exact ouRange_compression_mem_source_doubleCentralizer r s hrs e
    (ouRange_rotatedIncluded_mem_doubleCentralizer r s hrs e hT)

end FreeProbability.Fock

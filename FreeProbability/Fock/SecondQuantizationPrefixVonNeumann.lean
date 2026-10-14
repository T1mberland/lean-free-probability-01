import FreeProbability.Fock.SecondQuantizationPrefixCommutant
import FreeProbability.Fock.SecondQuantizationPrefixTransportCreators
import FreeProbability.Fock.SecondQuantizationPrefixTransportBoundedWOT

/-! # Literal double-commutant transport for the actual Fock representation -/

noncomputable section
namespace FreeProbability.Fock

/-- Multiplicative equivalences transport membership of literal double commutants. -/
theorem mulEquiv_mem_doubleCentralizer {R S : Type*} [Mul R] [Mul S]
    (f : R ≃* S) (s : Set R) {T : R} (hT : T ∈ Set.centralizer (Set.centralizer s)) :
    f T ∈ Set.centralizer (Set.centralizer (f '' s)) := by
  intro Q hQ
  apply f.symm.injective
  simp only [map_mul, f.symm_apply_apply]
  apply hT
  intro U hU
  apply f.injective
  simp only [map_mul, f.apply_symm_apply]
  exact hQ _ ⟨U, hU, rfl⟩

/-- The actual complete prefix representation preserves every literal double commutant. -/
theorem prefixOperatorEmbedding_mem_doubleCentralizer {I J : Type*}
    (s : Set (WordSpace I →L[ℂ] WordSpace I)) {T : WordSpace I →L[ℂ] WordSpace I}
    (hT : T ∈ Set.centralizer (Set.centralizer s)) :
    prefixOperatorEmbedding (J := J) T ∈
      Set.centralizer (Set.centralizer (prefixOperatorEmbedding (J := J) '' s)) := by
  have h := mulEquiv_mem_doubleCentralizer
    (prefixTailDecomposition (I := I) (J := J)).symm.conjStarAlgEquiv.toMulEquiv
    (hilbertAmplification '' s) (hilbertAmplification_mem_doubleCentralizer s hT)
  have he : (prefixOperatorEmbedding (I := I) (J := J) : _ → _) =
      fun x => (prefixTailDecomposition (I := I) (J := J)).symm.conjStarAlgEquiv.toMulEquiv
        (hilbertAmplification x) := by
    funext x
    rfl
  rw [he]
  simpa only [Set.image_image] using h

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The genuine ALL-operator tensor Fock embedding preserves literal double commutants. -/
theorem isometryPrefixEmbedding_mem_doubleCentralizer (V : H →ₗᵢ[ℂ] K)
    (s : Set (TensorFullFock H →L[ℂ] TensorFullFock H))
    {T : TensorFullFock H →L[ℂ] TensorFullFock H}
    (hT : T ∈ Set.centralizer (Set.centralizer s)) :
    isometryPrefixEmbedding V T ∈
      Set.centralizer (Set.centralizer (isometryPrefixEmbedding V '' s)) := by
  have hsource := mulEquiv_mem_doubleCentralizer
    (fullFockTensorDecomposition H).symm.conjStarAlgEquiv.toMulEquiv s hT
  have hprefix := prefixOperatorEmbedding_mem_doubleCentralizer
    (J := IsometryPrefixOutside V) _ hsource
  have htarget := mulEquiv_mem_doubleCentralizer
    (isometryPrefixTargetUnitary V).conjStarAlgEquiv.toMulEquiv _ hprefix
  have he : (isometryPrefixEmbedding V : _ → _) = fun x =>
      (isometryPrefixTargetUnitary V).conjStarAlgEquiv.toMulEquiv
        (prefixOperatorEmbedding ((fullFockTensorDecomposition H).symm.conjStarAlgEquiv.toMulEquiv x)) := by
    funext x
    rfl
  rw [he]
  simpa only [Set.image_image] using htarget

/-- The literal double commutant of ANY given field family maps into the
literal double commutant of its actual included fields. -/
theorem isometryPrefixEmbedding_mem_familyDoubleCentralizer {I : Type*}
    (V : H →ₗᵢ[ℂ] K) (e : I → H) {T : TensorFullFock H →L[ℂ] TensorFullFock H}
    (hT : T ∈ Set.centralizer (Set.centralizer (Set.range (tensorFamilyField e)))) :
    isometryPrefixEmbedding V T ∈ Set.centralizer
      (Set.centralizer (Set.range (tensorFamilyField (fun i => V (e i))))) := by
  have himage : isometryPrefixEmbedding V '' Set.range (tensorFamilyField e) =
      Set.range (tensorFamilyField (fun i => V (e i))) := by
    rw [← Set.range_comp']
    congr 1
    funext i
    exact isometryPrefixEmbedding_field V e i
  rw [← himage]
  exact isometryPrefixEmbedding_mem_doubleCentralizer V _ hT

end FreeProbability.Fock

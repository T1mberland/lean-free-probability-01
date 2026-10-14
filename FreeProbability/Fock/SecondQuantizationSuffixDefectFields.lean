import FreeProbability.Fock.SecondQuantizationSuffixDefectVectors

/-! # Exact annihilator and real-field defects for arbitrary prescribed families -/
noncomputable section
open scoped Classical
namespace FreeProbability.Fock
attribute [local irreducible] fullFockTensorDecomposition isometryPrefixTargetUnitary
  isometrySuffixEmbedding wordSuffixEmbedding
private theorem suffixAdjoint_commutator {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (A B : E →L[ℂ] E) :
    (A * B - B * A).adjoint = B.adjoint * A.adjoint - A.adjoint * B.adjoint := by
  change (A.comp B - B.comp A).adjoint = _
  rw [map_sub, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp]
  rfl

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Exact annihilator defect; the adjoint reverses commutator order, and both sides are negated. -/
theorem isometrySuffixEmbedding_annihilation_defect (V : H →ₗᵢ[ℂ] K)
    (T : TensorFullFock H →L[ℂ] TensorFullFock H) (h : H) :
    isometrySuffixEmbedding V T * tensorAnnihilation K (V h) -
      tensorAnnihilation K (V h) * isometrySuffixEmbedding V T =
    (secondQuantizationIsometry V).toContinuousLinearMap.comp
      ((T * tensorAnnihilation H h - tensorAnnihilation H h * T).comp
        (secondQuantizationIsometry V).toContinuousLinearMap.adjoint) := by
  have hs := isometrySuffixEmbedding_creation_defect V (star T) h
  change isometrySuffixEmbedding V (star T) * tensorCreation K (V h) -
    tensorCreation K (V h) * isometrySuffixEmbedding V (star T) =
      suffixSandwichContinuous V (star T * tensorCreation H h - tensorCreation H h * star T) at hs
  have ha := congrArg star hs
  rw [suffixSandwichContinuous_star] at ha
  change (isometrySuffixEmbedding V (star T) * tensorCreation K (V h) -
    tensorCreation K (V h) * isometrySuffixEmbedding V (star T)).adjoint =
    suffixSandwichContinuous V ((star T * tensorCreation H h - tensorCreation H h * star T).adjoint) at ha
  rw [suffixAdjoint_commutator, suffixAdjoint_commutator] at ha
  have hΦ : (isometrySuffixEmbedding V (star T)).adjoint = isometrySuffixEmbedding V T := by
    change star (isometrySuffixEmbedding V (star T)) = _
    rw [map_star, star_star]
  have hTadj : (star T).adjoint = T := by
    change T.adjoint.adjoint = T
    exact ContinuousLinearMap.adjoint_adjoint T
  rw [hΦ, hTadj] at ha
  have hn := congrArg Neg.neg ha
  rw [neg_sub, ← map_neg, neg_sub] at hn
  exact hn

/-- Exact real-field defect for ALL complex h, obtained by summing actual creator/adjoint defects. -/
theorem isometrySuffixEmbedding_field_defect (V : H →ₗᵢ[ℂ] K)
    (T : TensorFullFock H →L[ℂ] TensorFullFock H) (h : H) :
    isometrySuffixEmbedding V T * (tensorCreation K (V h) + tensorAnnihilation K (V h)) -
      (tensorCreation K (V h) + tensorAnnihilation K (V h)) * isometrySuffixEmbedding V T =
    (secondQuantizationIsometry V).toContinuousLinearMap.comp
      ((T * (tensorCreation H h + tensorAnnihilation H h) -
        (tensorCreation H h + tensorAnnihilation H h) * T).comp
          (secondQuantizationIsometry V).toContinuousLinearMap.adjoint) := by
  have hc := isometrySuffixEmbedding_creation_defect V T h
  have ha := isometrySuffixEmbedding_annihilation_defect V T h
  change isometrySuffixEmbedding V T * tensorCreation K (V h) -
    tensorCreation K (V h) * isometrySuffixEmbedding V T =
      suffixSandwichContinuous V (T * tensorCreation H h - tensorCreation H h * T) at hc
  change isometrySuffixEmbedding V T * tensorAnnihilation K (V h) -
    tensorAnnihilation K (V h) * isometrySuffixEmbedding V T =
      suffixSandwichContinuous V (T * tensorAnnihilation H h - tensorAnnihilation H h * T) at ha
  change isometrySuffixEmbedding V T * (tensorCreation K (V h) + tensorAnnihilation K (V h)) -
    (tensorCreation K (V h) + tensorAnnihilation K (V h)) * isometrySuffixEmbedding V T =
      suffixSandwichContinuous V (T * (tensorCreation H h + tensorAnnihilation H h) -
        (tensorCreation H h + tensorAnnihilation H h) * T)
  calc
    _ = (isometrySuffixEmbedding V T * tensorCreation K (V h) -
          tensorCreation K (V h) * isometrySuffixEmbedding V T) +
        (isometrySuffixEmbedding V T * tensorAnnihilation K (V h) -
          tensorAnnihilation K (V h) * isometrySuffixEmbedding V T) := by noncomm_ring
    _ = suffixSandwichContinuous V (T * tensorCreation H h - tensorCreation H h * T) +
        suffixSandwichContinuous V (T * tensorAnnihilation H h - tensorAnnihilation H h * T) :=
      congrArg₂ (· + ·) hc ha
    _ = suffixSandwichContinuous V ((T * tensorCreation H h - tensorCreation H h * T) +
        (T * tensorAnnihilation H h - tensorAnnihilation H h * T)) := (map_add _ _ _).symm
    _ = _ := congrArg (suffixSandwichContinuous V) (by noncomm_ring)

/-- Commutation with ONE specified source field suffices, without any other source-field assumptions. -/
theorem isometrySuffixEmbedding_commute_field (V : H →ₗᵢ[ℂ] K)
    (T : TensorFullFock H →L[ℂ] TensorFullFock H) (h : H)
    (hT : Commute T (tensorCreation H h + tensorAnnihilation H h)) :
    Commute (isometrySuffixEmbedding V T) (tensorCreation K (V h) + tensorAnnihilation K (V h)) := by
  have hd := isometrySuffixEmbedding_field_defect V T h
  change isometrySuffixEmbedding V T * (tensorCreation K (V h) + tensorAnnihilation K (V h)) -
    (tensorCreation K (V h) + tensorAnnihilation K (V h)) * isometrySuffixEmbedding V T =
      suffixSandwichContinuous V (T * (tensorCreation H h + tensorAnnihilation H h) -
        (tensorCreation H h + tensorAnnihilation H h) * T) at hd
  rw [hT.eq, sub_self, map_zero] at hd
  exact sub_eq_zero.mp hd

/-- Actual arbitrary prescribed-family commutant transport; no basis, spanning, countability or ON assumption. -/
theorem isometrySuffixEmbedding_commute_family_field {I : Type*} (V : H →ₗᵢ[ℂ] K)
    (e : I → H) (T : TensorFullFock H →L[ℂ] TensorFullFock H) (i : I)
    (hT : Commute T (tensorFamilyField e i)) :
    Commute (isometrySuffixEmbedding V T) (tensorFamilyField (fun j => V (e j)) i) :=
  isometrySuffixEmbedding_commute_field V T (e i) hT

end FreeProbability.Fock

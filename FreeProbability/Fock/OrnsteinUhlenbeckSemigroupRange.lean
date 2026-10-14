import FreeProbability.Fock.OrnsteinUhlenbeckSemigroupWickSpan

/-! # Actual generated-algebra range of the rotated completely positive dilation -/
noncomputable section
open scoped Classical InnerProductSpace
namespace FreeProbability.Fock
variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual rotated compression is continuous for the bounded-operator norms. -/
def rotatedCompressionContinuous (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1) :
    (TensorFullFock (DoubledHilbert H) →L[ℂ] TensorFullFock (DoubledHilbert H)) →L[ℂ]
      (TensorFullFock H →L[ℂ] TensorFullFock H) :=
  (rotatedFockCompression H r s hrs).toLinearMap.mkContinuous 1 (by
    intro T
    change ‖rotatedFockCompression H r s hrs T‖ ≤ 1 * ‖T‖
    rw [one_mul]
    exact norm_rotatedFockCompression_le H r s hrs T)

/-- Exact scaling of every actual included prescribed-family Wick word. -/
theorem rotatedCompression_included_familyWick (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1)
    (e : I → H) (w : List I) :
    rotatedFockCompression H r s hrs (familyWick (fun i => doubledFirst H (e i)) w) =
      (r : ℂ) ^ w.length • familyWick e w := by
  have hw : familyWick (fun i => doubledFirst H (e i)) w =
      tensorVectorWick ((w.map e).map (doubledFirst H)) := by
    unfold familyWick
    congr 1
    simp [List.map_map, Function.comp_def]
  rw [hw, rotatedFockCompression_vectorWick_first, List.length_map]
  rfl

/-- The actual rotated dilation takes the entire included generated norm closure into the original closure. -/
theorem rotatedCompression_includedFamily_range (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1)
    (e : I → H) {T : TensorFullFock (DoubledHilbert H) →L[ℂ] TensorFullFock (DoubledHilbert H)}
    (hT : T ∈ tensorFamilyAlgebra (fun i => doubledFirst H (e i))) :
    rotatedFockCompression H r s hrs T ∈ tensorFamilyAlgebra e := by
  have hp : ∀ T ∈ familyWickSpan (fun i => doubledFirst H (e i)),
      rotatedFockCompression H r s hrs T ∈ tensorFamilyAlgebra e := by
    intro T hT
    induction hT using Submodule.span_induction with
    | mem T hT =>
      obtain ⟨w, rfl⟩ := hT
      rw [rotatedCompression_included_familyWick]
      exact (tensorFamilyAlgebra e).smul_mem
        ((StarAlgebra.adjoin ℂ (Set.range (tensorFamilyField e))).le_topologicalClosure
          (familyWick_mem_polynomial e w)) _
    | zero =>
      rw [map_zero]
      exact (tensorFamilyAlgebra e).zero_mem
    | add T S _ _ hT hS =>
      rw [map_add]
      exact (tensorFamilyAlgebra e).add_mem hT hS
    | smul c T _ hT =>
      rw [map_smul]
      exact (tensorFamilyAlgebra e).smul_mem hT c
  have hc : IsClosed {T : TensorFullFock (DoubledHilbert H) →L[ℂ] TensorFullFock (DoubledHilbert H) |
      rotatedFockCompression H r s hrs T ∈ tensorFamilyAlgebra e} :=
    (StarAlgebra.adjoin ℂ (Set.range (tensorFamilyField e))).isClosed_topologicalClosure.preimage
      (rotatedCompressionContinuous r s hrs).continuous
  exact closure_minimal hp hc (tensorFamilyAlgebra_mem_closure_WickSpan _ hT)

/-- Actual rotated compression between the two literal C-star family closures. -/
def rotatedIncludedFamilyMap (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1) (e : I → H) :
    tensorFamilyAlgebra (fun i => doubledFirst H (e i)) →ₗ[ℂ] tensorFamilyAlgebra e where
  toFun T := ⟨rotatedFockCompression H r s hrs T, rotatedCompression_includedFamily_range r s hrs e T.property⟩
  map_add' T S := Subtype.ext (map_add (rotatedFockCompression H r s hrs).toLinearMap
    (T : TensorFullFock (DoubledHilbert H) →L[ℂ] TensorFullFock (DoubledHilbert H)) S)
  map_smul' c T := Subtype.ext (map_smul (rotatedFockCompression H r s hrs).toLinearMap c
    (T : TensorFullFock (DoubledHilbert H) →L[ℂ] TensorFullFock (DoubledHilbert H)))

@[simp] theorem rotatedIncludedFamilyMap_one (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1) (e : I → H) :
    rotatedIncludedFamilyMap r s hrs e 1 = 1 := Subtype.ext (rotatedFockCompression_one H r s hrs)

theorem norm_rotatedIncludedFamilyMap_le (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1) (e : I → H)
    (T : tensorFamilyAlgebra (fun i => doubledFirst H (e i))) :
    ‖rotatedIncludedFamilyMap r s hrs e T‖ ≤ ‖T‖ := norm_rotatedFockCompression_le H r s hrs T

/-- The actual vacuum states correspond under the literal generated-algebra restriction. -/
theorem rotatedIncludedFamilyMap_expectation (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1) (e : I → H)
    (T : tensorFamilyAlgebra (fun i => doubledFirst H (e i))) :
    (tensorFamilyVacuumState e).expectation (rotatedIncludedFamilyMap r s hrs e T) =
      (tensorFamilyVacuumState (fun i => doubledFirst H (e i))).expectation T := by
  change (tensorVacuumState H).expectation (rotatedFockCompression H r s hrs T) =
    (tensorVacuumState (DoubledHilbert H)).expectation T
  rw [tensorVacuumState_expectation, tensorVacuumState_expectation]
  exact rotatedFockCompression_vacuum_expectation H r s hrs T

end FreeProbability.Fock

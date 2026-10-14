import FreeProbability.Fock.SecondQuantizationWOTGeneratedReducing

/-! # Actual star-homomorphic compression of WOT-generated field algebras -/
noncomputable section
open scoped Classical
namespace FreeProbability.Fock
variable {I H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem includedCompressionWOT_field (V : H →ₗᵢ[ℂ] K) (e : I → H) (i : I) :
    secondQuantizationCompressionWOT V
      (ContinuousLinearMapWOT.ofCLM (tensorFamilyField (fun j => V (e j)) i)) =
      ContinuousLinearMapWOT.ofCLM (tensorFamilyField e i) :=
  congrArg ContinuousLinearMapWOT.ofCLM (includedCompression_field V e i)

/-- Actual compression maps the full included WOT closure into the original WOT closure. -/
theorem includedCompressionWOT_maps_into (V : H →ₗᵢ[ℂ] K) (e : I → H)
    {T : TensorFullFock K →WOT[ℂ] TensorFullFock K}
    (hT : T ∈ tensorFamilyWOTAlgebra (fun i => V (e i))) :
    secondQuantizationCompressionWOT V T ∈ tensorFamilyWOTAlgebra e := by
  have hp : ∀ T ∈ StarAlgebra.adjoin ℂ (Set.range (fun i =>
      ContinuousLinearMapWOT.ofCLM (tensorFamilyField (fun j => V (e j)) i))),
      secondQuantizationCompressionWOT V T ∈ tensorFamilyWOTAlgebra e := by
    intro T h
    induction h using StarAlgebra.adjoin_induction with
    | mem T h =>
      obtain ⟨i, rfl⟩ := h
      rw [includedCompressionWOT_field]
      exact (StarAlgebra.adjoin ℂ (Set.range (fun j =>
        ContinuousLinearMapWOT.ofCLM (tensorFamilyField e j)))).le_topologicalClosure
        (StarAlgebra.subset_adjoin ℂ _ (Set.mem_range_self i))
    | algebraMap c =>
      change ContinuousLinearMapWOT.ofCLM
        (secondQuantizationCompression V (algebraMap ℂ _ c)) ∈ _
      rw [Algebra.algebraMap_eq_smul_one, map_smul, secondQuantizationCompression_one]
      exact (tensorFamilyWOTAlgebra e).smul_mem (tensorFamilyWOTAlgebra e).one_mem c
    | add T S _ _ hT hS =>
      change ContinuousLinearMapWOT.ofCLM (secondQuantizationCompression V (T.toCLM + S.toCLM)) ∈ _
      rw [map_add]
      exact (tensorFamilyWOTAlgebra e).add_mem hT hS
    | mul T S _ hS hT' hS' =>
      rw [tensorFamilyWOTAlgebra_compression_mul V e T S
        ((StarAlgebra.adjoin ℂ (Set.range (fun i =>
          ContinuousLinearMapWOT.ofCLM (tensorFamilyField (fun j => V (e j)) i)))).le_topologicalClosure hS)]
      exact (tensorFamilyWOTAlgebra e).mul_mem hT' hS'
    | star T _ hT =>
      change ContinuousLinearMapWOT.ofCLM (secondQuantizationCompression V (star T.toCLM)) ∈ _
      rw [inclusion_compression_star]
      exact star_mem hT
  have hc : IsClosed {T : TensorFullFock K →WOT[ℂ] TensorFullFock K |
      secondQuantizationCompressionWOT V T ∈ tensorFamilyWOTAlgebra e} :=
    (StarAlgebra.adjoin ℂ (Set.range (fun i =>
      ContinuousLinearMapWOT.ofCLM (tensorFamilyField e i)))).isClosed_topologicalClosure.preimage
      (secondQuantizationCompressionWOT_continuous V)
  change T ∈ (StarAlgebra.adjoin ℂ (Set.range (fun i =>
    ContinuousLinearMapWOT.ofCLM (tensorFamilyField (fun j => V (e j)) i)))).topologicalClosure at hT
  rw [← SetLike.mem_coe, StarSubalgebra.topologicalClosure_coe] at hT
  exact closure_minimal hp hc hT

/-- Actual unital star-homomorphic compression, with both genuine WOT-generated codomains. -/
def includedFamilyWOTCompression (V : H →ₗᵢ[ℂ] K) (e : I → H) :
    tensorFamilyWOTAlgebra (fun i => V (e i)) →⋆ₐ[ℂ] tensorFamilyWOTAlgebra e where
  toFun T := ⟨secondQuantizationCompressionWOT V T, includedCompressionWOT_maps_into V e T.property⟩
  map_one' := Subtype.ext (congrArg ContinuousLinearMapWOT.ofCLM (secondQuantizationCompression_one V))
  map_mul' T S := Subtype.ext (tensorFamilyWOTAlgebra_compression_mul V e T S S.property)
  map_zero' := Subtype.ext (congrArg ContinuousLinearMapWOT.ofCLM (map_zero (secondQuantizationCompression V)))
  map_add' T S := Subtype.ext (congrArg ContinuousLinearMapWOT.ofCLM
    (map_add (secondQuantizationCompression V) T.val.toCLM S.val.toCLM))
  commutes' c := Subtype.ext (by
    change ContinuousLinearMapWOT.ofCLM (secondQuantizationCompression V (algebraMap ℂ _ c)) = _
    rw [Algebra.algebraMap_eq_smul_one, map_smul, secondQuantizationCompression_one]
    rfl)
  map_star' T := Subtype.ext (congrArg ContinuousLinearMapWOT.ofCLM (inclusion_compression_star V T.val.toCLM))

/-- Restricted compression remains genuinely continuous in the induced weak operator topologies. -/
theorem includedFamilyWOTCompression_continuous (V : H →ₗᵢ[ℂ] K) (e : I → H) :
    Continuous (includedFamilyWOTCompression V e) :=
  ((secondQuantizationCompressionWOT_continuous V).comp continuous_subtype_val).subtype_mk _

end FreeProbability.Fock

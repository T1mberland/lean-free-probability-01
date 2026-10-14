import FreeProbability.Fock.OrnsteinUhlenbeckEmbeddingReducing

/-! # Actual star-homomorphic compression of the included generated algebra -/
noncomputable section
open scoped Classical
namespace FreeProbability.Fock
variable {I H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The actual compression is continuous in operator norm on the full ambient algebra. -/
def ouCompressionContinuous (V : H →ₗᵢ[ℂ] K) :
    (TensorFullFock K →L[ℂ] TensorFullFock K) →L[ℂ] (TensorFullFock H →L[ℂ] TensorFullFock H) :=
  (secondQuantizationCompression V).mkContinuous 1 (by
    intro T
    simpa only [one_mul] using norm_secondQuantizationCompression_le V T)

/-- Restriction of actual compression is a genuine unital star homomorphism on the included closure. -/
def includedCompressionAmbient (V : H →ₗᵢ[ℂ] K) (e : I → H) :
    tensorFamilyAlgebra (fun i => V (e i)) →⋆ₐ[ℂ] (TensorFullFock H →L[ℂ] TensorFullFock H) where
  toAlgHom := AlgHom.ofLinearMap
    ((secondQuantizationCompression V).comp (tensorFamilyAlgebra (fun i => V (e i))).val.toLinearMap)
    (secondQuantizationCompression_one V)
    (fun T S => tensorFamilyAlgebra_compression_mul V e T S S.property)
  map_star' T := inclusion_compression_star V T

/-- Actual included fields compress to precisely the original family fields. -/
theorem includedCompression_field (V : H →ₗᵢ[ℂ] K) (e : I → H) (i : I) :
    secondQuantizationCompression V (tensorFamilyField (fun j => V (e j)) i) = tensorFamilyField e i := by
  change secondQuantizationCompression V (tensorCreation K (V (e i)) + tensorAnnihilation K (V (e i))) = _
  rw [map_add, inclusion_compression_creation]
  have ha : secondQuantizationCompression V (tensorAnnihilation K (V (e i))) = tensorAnnihilation H (e i) := by
    change secondQuantizationCompression V (star (tensorCreation K (V (e i)))) = star (tensorCreation H (e i))
    rw [inclusion_compression_star, inclusion_compression_creation]
  rw [ha]
  rfl

/-- Actual compression maps the entire included norm closure into the original literal family closure. -/
theorem includedCompression_maps_into (V : H →ₗᵢ[ℂ] K) (e : I → H)
    {T : TensorFullFock K →L[ℂ] TensorFullFock K}
    (hT : T ∈ tensorFamilyAlgebra (fun i => V (e i))) :
    secondQuantizationCompression V T ∈ tensorFamilyAlgebra e := by
  have hp : ∀ T ∈ StarAlgebra.adjoin ℂ (Set.range (tensorFamilyField (fun i => V (e i)))),
      secondQuantizationCompression V T ∈ tensorFamilyAlgebra e := by
    intro T h
    induction h using StarAlgebra.adjoin_induction with
    | mem T h =>
      obtain ⟨i, rfl⟩ := h
      rw [includedCompression_field]
      exact (tensorFamilyGenerator e i).property
    | algebraMap c =>
      rw [Algebra.algebraMap_eq_smul_one, map_smul, secondQuantizationCompression_one]
      exact (tensorFamilyAlgebra e).smul_mem (tensorFamilyAlgebra e).one_mem c
    | add T S _ _ hT hS =>
      rw [map_add]
      exact (tensorFamilyAlgebra e).add_mem hT hS
    | mul T S _ hS hT' hS' =>
      rw [tensorFamilyAlgebra_compression_mul V e T S
        ((StarAlgebra.adjoin ℂ (Set.range (tensorFamilyField (fun i => V (e i))))).le_topologicalClosure hS)]
      exact (tensorFamilyAlgebra e).mul_mem hT' hS'
    | star T _ hT =>
      rw [inclusion_compression_star]
      exact star_mem hT
  have hc : IsClosed {T : TensorFullFock K →L[ℂ] TensorFullFock K |
      secondQuantizationCompression V T ∈ tensorFamilyAlgebra e} :=
    (StarAlgebra.adjoin ℂ (Set.range (tensorFamilyField e))).isClosed_topologicalClosure.preimage
      (ouCompressionContinuous V).continuous
  change T ∈ (StarAlgebra.adjoin ℂ (Set.range (tensorFamilyField (fun i => V (e i))))).topologicalClosure at hT
  rw [← SetLike.mem_coe, StarSubalgebra.topologicalClosure_coe] at hT
  exact closure_minimal hp hc hT

/-- Actual restricted compression, with its codomain the original literal generated C-star algebra. -/
def includedFamilyCompression (V : H →ₗᵢ[ℂ] K) (e : I → H) :
    tensorFamilyAlgebra (fun i => V (e i)) →⋆ₐ[ℂ] tensorFamilyAlgebra e where
  toFun T := ⟨secondQuantizationCompression V T, includedCompression_maps_into V e T.property⟩
  map_one' := Subtype.ext (secondQuantizationCompression_one V)
  map_mul' T S := Subtype.ext (tensorFamilyAlgebra_compression_mul V e T S S.property)
  map_zero' := Subtype.ext (map_zero (secondQuantizationCompression V))
  map_add' T S := Subtype.ext (map_add (includedCompressionAmbient V e) T S)
  commutes' c := Subtype.ext ((includedCompressionAmbient V e).commutes c)
  map_star' T := Subtype.ext (inclusion_compression_star V T)

@[simp] theorem includedFamilyCompression_generator (V : H →ₗᵢ[ℂ] K) (e : I → H) (i : I) :
    includedFamilyCompression V e (tensorFamilyGenerator (fun j => V (e j)) i) = tensorFamilyGenerator e i :=
  Subtype.ext (includedCompression_field V e i)

end FreeProbability.Fock

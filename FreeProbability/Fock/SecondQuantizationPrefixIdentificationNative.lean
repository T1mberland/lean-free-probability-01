import FreeProbability.Fock.SecondQuantizationPrefixTransportBoundedWOT
import FreeProbability.Fock.OrnsteinUhlenbeckEmbeddingEquiv

/-! # Actual prefix representation equals the native included C-star embedding -/
noncomputable section
open scoped Classical
namespace FreeProbability.Fock
variable {I H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Exact field action and norm continuity send the whole native closure into the included closure. -/
theorem isometryPrefixEmbedding_maps_native (V : H →ₗᵢ[ℂ] K) (e : I → H)
    {T : TensorFullFock H →L[ℂ] TensorFullFock H} (hT : T ∈ tensorFamilyAlgebra e) :
    isometryPrefixEmbedding V T ∈ tensorFamilyAlgebra (fun i => V (e i)) := by
  let B := (tensorFamilyAlgebra (fun i => V (e i))).comap (isometryPrefixEmbedding V)
  have hp : StarAlgebra.adjoin ℂ (Set.range (tensorFamilyField e)) ≤ B := by
    apply StarAlgebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    change isometryPrefixEmbedding V (tensorFamilyField e i) ∈ tensorFamilyAlgebra (fun j => V (e j))
    rw [isometryPrefixEmbedding_field]
    exact (tensorFamilyGenerator (fun j => V (e j)) i).property
  have hc : IsClosed (B : Set (TensorFullFock H →L[ℂ] TensorFullFock H)) :=
    (StarAlgebra.adjoin ℂ (Set.range (tensorFamilyField (fun i => V (e i))))).isClosed_topologicalClosure.preimage
      (isometryPrefixEmbeddingContinuous V).continuous
  exact StarSubalgebra.topologicalClosure_minimal hp hc hT

/-- Actual restriction of the all-operator prefix representation to the native family C-star algebra. -/
def prefixNativeEmbedding (V : H →ₗᵢ[ℂ] K) (e : I → H) :
    tensorFamilyAlgebra e →⋆ₐ[ℂ] tensorFamilyAlgebra (fun i => V (e i)) where
  toFun T := ⟨isometryPrefixEmbedding V T, isometryPrefixEmbedding_maps_native V e T.property⟩
  map_one' := Subtype.ext (map_one (isometryPrefixEmbedding V))
  map_mul' T S := Subtype.ext (map_mul (isometryPrefixEmbedding V) T.val S.val)
  map_zero' := Subtype.ext (map_zero (isometryPrefixEmbedding V))
  map_add' T S := Subtype.ext (map_add (isometryPrefixEmbedding V) T.val S.val)
  commutes' c := Subtype.ext ((isometryPrefixEmbedding V).commutes c)
  map_star' T := Subtype.ext (map_star (isometryPrefixEmbedding V) T.val)

@[simp] theorem prefixNativeEmbedding_generator (V : H →ₗᵢ[ℂ] K) (e : I → H) (i : I) :
    prefixNativeEmbedding V e (tensorFamilyGenerator e i) = tensorFamilyGenerator (fun j => V (e j)) i :=
  Subtype.ext (isometryPrefixEmbedding_field V e i)

def prefixNativeEmbeddingContinuous (V : H →ₗᵢ[ℂ] K) (e : I → H) :
    tensorFamilyAlgebra e →L[ℂ] tensorFamilyAlgebra (fun i => V (e i)) :=
  (prefixNativeEmbedding V e).toAlgHom.toLinearMap.mkContinuous 1 (by
    intro T
    change ‖isometryPrefixEmbedding V T.val‖ ≤ 1 * ‖T‖
    rw [NonUnitalStarAlgHom.norm_map (isometryPrefixEmbedding V) (isometryPrefixEmbedding_injective V),
      one_mul]
    rfl)

def nativeIncludedEmbeddingContinuous (V : H →ₗᵢ[ℂ] K) (e : I → H) (he : Orthonormal ℂ e) :
    tensorFamilyAlgebra e →L[ℂ] tensorFamilyAlgebra (fun i => V (e i)) :=
  (includedFamilyEmbedding V e he).toAlgHom.toLinearMap.mkContinuous 1 (by
    intro T
    change ‖includedFamilyEmbedding V e he T‖ ≤ 1 * ‖T‖
    rw [includedFamilyEmbedding_norm, one_mul])

/-- Exact identification on the entire native norm closure by polynomial star-algebra density. -/
theorem prefixNativeEmbedding_eq_includedFamilyEmbedding (V : H →ₗᵢ[ℂ] K) (e : I → H)
    (he : Orthonormal ℂ e) : prefixNativeEmbedding V e = includedFamilyEmbedding V e he := by
  let P := StarAlgebra.adjoin ℂ (Set.range (tensorFamilyField e))
  let j : P →⋆ₐ[ℂ] tensorFamilyAlgebra e := StarSubalgebra.inclusion P.le_topologicalClosure
  have hd : DenseRange j := (denseRange_inclusion_iff P.le_topologicalClosure).mpr Set.Subset.rfl
  have hp : (prefixNativeEmbedding V e).comp j = (includedFamilyEmbedding V e he).comp j := by
    apply StarAlgHom.ext_adjoin
    intro T hT
    obtain ⟨i, hi⟩ := hT
    have hgen : j T = tensorFamilyGenerator e i := Subtype.ext hi.symm
    change prefixNativeEmbedding V e (j T) = includedFamilyEmbedding V e he (j T)
    rw [hgen, prefixNativeEmbedding_generator, includedFamilyEmbedding_generator]
  have hc : IsClosed {T : tensorFamilyAlgebra e |
      prefixNativeEmbedding V e T = includedFamilyEmbedding V e he T} :=
    isClosed_eq (prefixNativeEmbeddingContinuous V e).continuous
      (nativeIncludedEmbeddingContinuous V e he).continuous
  have hle : closure (Set.range j) ⊆ {T : tensorFamilyAlgebra e |
      prefixNativeEmbedding V e T = includedFamilyEmbedding V e he T} :=
    closure_minimal (by
      rintro _ ⟨T, rfl⟩
      exact DFunLike.congr_fun hp T) hc
  apply DFunLike.ext
  intro T
  apply hle
  rw [hd.closure_range]
  trivial

end FreeProbability.Fock

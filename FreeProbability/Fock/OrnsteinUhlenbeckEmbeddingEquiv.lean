import FreeProbability.Fock.OrnsteinUhlenbeckEmbeddingCompression
import Mathlib.Analysis.CStarAlgebra.Hom

/-! # The genuine included-family C-star embedding, obtained from actual faithful compression -/
noncomputable section
open scoped Classical
namespace FreeProbability.Fock
variable {I H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Actual normalized vacuum states correspond under the restricted compression. -/
theorem includedFamilyCompression_expectation (V : H →ₗᵢ[ℂ] K) (e : I → H)
    (T : tensorFamilyAlgebra (fun i => V (e i))) :
    (tensorFamilyVacuumState e).expectation (includedFamilyCompression V e T) =
      (tensorFamilyVacuumState (fun i => V (e i))).expectation T := by
  change (tensorVacuumState H).expectation (secondQuantizationCompression V T) =
    (tensorVacuumState K).expectation T
  rw [tensorVacuumState_expectation, tensorVacuumState_expectation]
  exact secondQuantizationCompression_vacuum_expectation V T

/-- Genuine injectivity, from the proved native orthonormal-family faithfulness. -/
theorem includedFamilyCompression_injective (V : H →ₗᵢ[ℂ] K) (e : I → H) (he : Orthonormal ℂ e) :
    Function.Injective (includedFamilyCompression V e) := by
  have hfaith := tensorFamilyVacuumState_faithful (fun i => V (e i)) (he.comp_linearIsometry V)
  have hker : ∀ T, includedFamilyCompression V e T = 0 → T = 0 := by
    intro T hT
    apply hfaith T
    have hz := includedFamilyCompression_expectation V e (star T * T)
    rw [map_mul, map_star, hT] at hz
    have hz0 : star (0 : tensorFamilyAlgebra e) * 0 = 0 := by
      apply Subtype.ext
      simp
    rw [hz0, map_zero] at hz
    exact hz.symm
  intro T S hTS
  have hh : includedFamilyCompression V e (T - S) = 0 :=
    (map_sub (includedFamilyCompression V e).toAlgHom T S).trans
      ((congrArg (fun z : tensorFamilyAlgebra e => z - includedFamilyCompression V e S) hTS).trans
        (sub_self _))
  exact sub_eq_zero.mp (hker (T - S) hh)

/-- The ambient compression star homomorphism is also injective. -/
theorem includedCompressionAmbient_injective (V : H →ₗᵢ[ℂ] K) (e : I → H) (he : Orthonormal ℂ e) :
    Function.Injective (includedCompressionAmbient V e) := by
  intro T S hTS
  apply includedFamilyCompression_injective V e he
  exact Subtype.ext hTS

/-- The actual image is closed in the entire original bounded-operator algebra. -/
theorem includedCompressionAmbient_closed_range (V : H →ₗᵢ[ℂ] K) (e : I → H) (he : Orthonormal ℂ e) :
    IsClosed (Set.range (includedCompressionAmbient V e)) :=
  (NonUnitalStarAlgHom.isometry (includedCompressionAmbient V e)
    (includedCompressionAmbient_injective V e he)).isClosedEmbedding.isClosed_range

/-- The image contains every original field and hence the entire original generated norm closure. -/
theorem includedFamilyCompression_surjective (V : H →ₗᵢ[ℂ] K) (e : I → H) (he : Orthonormal ℂ e) :
    Function.Surjective (includedFamilyCompression V e) := by
  have hp : StarAlgebra.adjoin ℂ (Set.range (tensorFamilyField e)) ≤ (includedCompressionAmbient V e).range := by
    apply StarAlgebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    exact ⟨tensorFamilyGenerator (fun j => V (e j)) i, includedCompression_field V e i⟩
  have hc : IsClosed ((includedCompressionAmbient V e).range : Set (TensorFullFock H →L[ℂ] TensorFullFock H)) :=
    includedCompressionAmbient_closed_range V e he
  intro T
  have ht := StarSubalgebra.topologicalClosure_minimal hp hc T.property
  obtain ⟨S, hS⟩ := ht
  exact ⟨S, Subtype.ext hS⟩

/-- Actual onto isometric star-algebra equivalence between the two literal norm closures. -/
def includedFamilyEquiv (V : H →ₗᵢ[ℂ] K) (e : I → H) (he : Orthonormal ℂ e) :
    tensorFamilyAlgebra (fun i => V (e i)) ≃⋆ₐ[ℂ] tensorFamilyAlgebra e :=
  StarAlgEquiv.ofBijective (includedFamilyCompression V e)
    ⟨includedFamilyCompression_injective V e he, includedFamilyCompression_surjective V e he⟩

/-- The inverse equivalence is the actual unital C-star embedding of the original family algebra. -/
def includedFamilyEmbedding (V : H →ₗᵢ[ℂ] K) (e : I → H) (he : Orthonormal ℂ e) :
    tensorFamilyAlgebra e →⋆ₐ[ℂ] tensorFamilyAlgebra (fun i => V (e i)) :=
  (includedFamilyEquiv V e he).symm.toStarAlgHom

@[simp] theorem includedFamilyEmbedding_generator (V : H →ₗᵢ[ℂ] K) (e : I → H)
    (he : Orthonormal ℂ e) (i : I) :
    includedFamilyEmbedding V e he (tensorFamilyGenerator e i) =
      tensorFamilyGenerator (fun j => V (e j)) i := by
  apply (includedFamilyEquiv V e he).injective
  change includedFamilyEquiv V e he ((includedFamilyEquiv V e he).symm (tensorFamilyGenerator e i)) = _
  rw [StarAlgEquiv.apply_symm_apply]
  exact (includedFamilyCompression_generator V e i).symm

@[simp] theorem includedFamilyEmbedding_norm (V : H →ₗᵢ[ℂ] K) (e : I → H)
    (he : Orthonormal ℂ e) (T : tensorFamilyAlgebra e) :
    ‖includedFamilyEmbedding V e he T‖ = ‖T‖ := StarAlgEquiv.norm_map (includedFamilyEquiv V e he).symm T

end FreeProbability.Fock

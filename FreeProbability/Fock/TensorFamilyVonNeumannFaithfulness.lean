import FreeProbability.Fock.TensorFamilyVonNeumann
import FreeProbability.Fock.SecondQuantizationPrefixVonNeumann

/-! # Faithful tracial vacuum for arbitrary ON families on actual tensor double commutants -/
noncomputable section
namespace FreeProbability.Fock
variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace OrthonormalFamilyExtension
variable {e : I → H} (d : OrthonormalFamilyExtension e)

/-- Actual adapted unitary transport embeds the given double commutant into the full word double commutant. -/
theorem tensorFamilyVonNeumann_maps_into_fullWord
    {T : TensorFullFock H →L[ℂ] TensorFullFock H} (hT : T ∈ tensorFamilyVonNeumannAlgebra e) :
    d.tensorOperatorTransport.symm T ∈ wordSemicircularVonNeumannAlgebra d.indices := by
  have hraw := (tensorFamilyVonNeumannAlgebra_mem_iff e).mp hT
  have hsource := mulEquiv_mem_doubleCentralizer d.tensorOperatorTransport.symm.toMulEquiv
    (Set.range (tensorFamilyField e)) hraw
  have hf : (d.tensorOperatorTransport.symm.toMulEquiv :
      (TensorFullFock H →L[ℂ] TensorFullFock H) → (d.Space →L[ℂ] d.Space)) =
      d.tensorOperatorTransport.symm := by
    funext X
    rfl
  rw [hf] at hsource
  have hi (i : I) : d.tensorOperatorTransport.symm (tensorFamilyField e i) = d.field i := by
    apply d.tensorOperatorTransport.injective
    change d.tensorOperatorTransport (d.tensorOperatorTransport.symm (tensorFamilyField e i)) =
      d.tensorOperatorTransport (d.field i)
    rw [StarAlgEquiv.apply_symm_apply, d.tensorOperatorTransport_field]
    rfl
  have himage : d.tensorOperatorTransport.symm '' Set.range (tensorFamilyField e) = Set.range d.field := by
    rw [← Set.range_comp']
    congr 1
    funext i
    exact hi i
  rw [himage] at hsource
  have hsub : Set.range d.field ⊆ (semicircularAlgebra d.indices : Set (d.Space →L[ℂ] d.Space)) := by
    rintro X ⟨i, rfl⟩
    rw [d.field_eq_semicircular]
    exact semicircular_mem_algebra _
  rw [wordSemicircularVonNeumannAlgebra_mem_iff]
  exact Set.centralizer_subset (Set.centralizer_subset hsub) hsource

include d in
theorem tensorFamilyVonNeumannVacuumState_isFaithful :
    IsFaithful (tensorFamilyVonNeumannVacuumState e).toProbabilitySpace := by
  intro T hzero
  have hword := d.tensorFamilyVonNeumann_maps_into_fullWord T.property
  have hz : vacuumExpectation
      (star (d.tensorOperatorTransport.symm T) * d.tensorOperatorTransport.symm T) = 0 := by
    have h := d.tensorOperatorTransport_symm_expectation
      (star (T : TensorFullFock H →L[ℂ] TensorFullFock H) * T)
    rw [map_mul, map_star] at h
    exact h.trans hzero
  apply Subtype.ext
  apply d.tensorOperatorTransport.symm.injective
  change d.tensorOperatorTransport.symm (T : TensorFullFock H →L[ℂ] TensorFullFock H) =
    d.tensorOperatorTransport.symm 0
  rw [map_zero]
  exact wordSemicircularVonNeumannAlgebra_vacuum_faithful hword hz

include d in
theorem tensorFamilyVonNeumannVacuumState_isTracial :
    IsTracial (tensorFamilyVonNeumannVacuumState e).toProbabilitySpace := by
  intro T U
  have hT := d.tensorFamilyVonNeumann_maps_into_fullWord T.property
  have hU := d.tensorFamilyVonNeumann_maps_into_fullWord U.property
  have ht := d.tensorOperatorTransport_symm_expectation
    ((T : TensorFullFock H →L[ℂ] TensorFullFock H) * U)
  have hu := d.tensorOperatorTransport_symm_expectation
    ((U : TensorFullFock H →L[ℂ] TensorFullFock H) * T)
  rw [map_mul] at ht hu
  exact ht.symm.trans ((wordSemicircularVonNeumannAlgebra_vacuum_tracial hT hU).trans hu)

end OrthonormalFamilyExtension

theorem tensorFamilyVonNeumannVacuumState_faithful (e : I → H) (he : Orthonormal ℂ e) :
    IsFaithful (tensorFamilyVonNeumannVacuumState e).toProbabilitySpace :=
  (orthonormalFamilyExtension he).tensorFamilyVonNeumannVacuumState_isFaithful

theorem tensorFamilyVonNeumannVacuumState_tracial (e : I → H) (he : Orthonormal ℂ e) :
    IsTracial (tensorFamilyVonNeumannVacuumState e).toProbabilitySpace :=
  (orthonormalFamilyExtension he).tensorFamilyVonNeumannVacuumState_isTracial

end FreeProbability.Fock

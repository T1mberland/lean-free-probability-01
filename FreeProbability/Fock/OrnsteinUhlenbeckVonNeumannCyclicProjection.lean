import FreeProbability.Fock.OrnsteinUhlenbeckVonNeumannVacuumL2
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! The original native-family cyclic Hilbert space reduces the given field generators. -/
noncomputable section
open scoped Classical InnerProductSpace
namespace FreeProbability.Fock
section General
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A genuinely symmetric bounded operator preserving a closed Hilbert subspace commutes
with its actual orthogonal projection. -/
theorem ouCyclicProjection_commute_of_invariant (K : Submodule ℂ E) [CompleteSpace K]
    (T : E →L[ℂ] E) (hT : T.adjoint = T) (hK : ∀ f ∈ K, T f ∈ K) :
    Commute K.starProjection T := by
  apply ContinuousLinearMap.ext
  intro f
  change K.starProjection (T f) = T (K.starProjection f)
  apply K.eq_starProjection_of_mem_of_inner_eq_zero (hK _ (K.starProjection_apply_mem f))
  intro w hw
  rw [← map_sub, ← T.adjoint_inner_right, hT]
  exact K.starProjection_inner_eq_zero f (T w) (hK w hw)
end General

variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The prescribed generator as an actual element of its original norm-closed algebra. -/
def ouCyclicNativeField (e : I → H) (i : I) : tensorFamilyAlgebra e :=
  ⟨tensorFamilyField e i, (StarAlgebra.adjoin ℂ (Set.range (tensorFamilyField e))).le_topologicalClosure
    (StarAlgebra.subset_adjoin ℂ _ (Set.mem_range_self i))⟩

/-- Each actual given field preserves the ORIGINAL family cyclic Hilbert closure. -/
theorem ouCyclic_field_mem (e : I → H) (i : I) {f : TensorFullFock H}
    (hf : f ∈ familyCyclicSpace e) : tensorFamilyField e i f ∈ familyCyclicSpace e := by
  have hp : ((familyVacuumVector e).range : Set (TensorFullFock H)) ⊆
      (tensorFamilyField e i) ⁻¹' (familyCyclicSpace e : Set _) := by
    rintro _ ⟨T, rfl⟩
    exact familyVacuumVector_mem_cyclic e (ouCyclicNativeField e i * T)
  have hc : IsClosed ((tensorFamilyField e i) ⁻¹' (familyCyclicSpace e : Set _)) :=
    (inferInstance : IsClosed (familyCyclicSpace e : Set (TensorFullFock H))).preimage
      (tensorFamilyField e i).continuous
  change f ∈ closure ((familyVacuumVector e).range : Set (TensorFullFock H)) at hf
  exact closure_minimal hp hc hf

/-- Actual orthogonal projection onto the original complete family cyclic space. -/
def ouFamilyCyclicProjection (e : I → H) : TensorFullFock H →L[ℂ] TensorFullFock H :=
  (familyCyclicSpace e).starProjection

 theorem ouFamilyCyclicProjection_commute_field (e : I → H) (i : I) :
    Commute (ouFamilyCyclicProjection e) (tensorFamilyField e i) :=
  ouCyclicProjection_commute_of_invariant (familyCyclicSpace e) (tensorFamilyField e i)
    (ou_tensorFamilyField_adjoint e i) (fun _ hf => ouCyclic_field_mem e i hf)

 theorem ouFamilyCyclicProjection_mem_commutant (e : I → H) :
    ouFamilyCyclicProjection e ∈ Set.centralizer (Set.range (tensorFamilyField e)) := by
  apply Set.mem_centralizer_iff.mpr
  rintro _ ⟨i, rfl⟩
  exact (ouFamilyCyclicProjection_commute_field e i).symm.eq

 theorem ouCyclic_vacuum_mem (e : I → H) : tensorVacuum H ∈ familyCyclicSpace e :=
  familyVacuumVector_mem_cyclic e 1

@[simp] theorem ouFamilyCyclicProjection_vacuum (e : I → H) :
    ouFamilyCyclicProjection e (tensorVacuum H) = tensorVacuum H :=
  (familyCyclicSpace e).starProjection_eq_self_iff.mpr (ouCyclic_vacuum_mem e)

end FreeProbability.Fock

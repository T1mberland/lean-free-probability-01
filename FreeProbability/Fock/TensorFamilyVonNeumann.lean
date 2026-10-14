import FreeProbability.Fock.WordVonNeumannTrace
import FreeProbability.Fock.OrnsteinUhlenbeckEmbeddingReducing

/-! # Literal prescribed-field double commutants on completed tensor Fock space -/
noncomputable section
namespace FreeProbability.Fock
variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual prescribed-family double commutant, as a closed star algebra. -/
def tensorFamilyDoubleAlgebra (e : I → H) :
    StarSubalgebra ℂ (TensorFullFock H →L[ℂ] TensorFullFock H) :=
  StarSubalgebra.centralizer ℂ
    (StarSubalgebra.centralizer ℂ (Set.range (tensorFamilyField e)) :
      Set (TensorFullFock H →L[ℂ] TensorFullFock H))

theorem tensorFamilyDoubleAlgebra_coe (e : I → H) :
    (tensorFamilyDoubleAlgebra e : Set (TensorFullFock H →L[ℂ] TensorFullFock H)) =
      Set.centralizer (Set.centralizer (Set.range (tensorFamilyField e))) := by
  let C := StarSubalgebra.centralizer ℂ (Set.range (tensorFamilyField e))
  have hc : (C : Set (TensorFullFock H →L[ℂ] TensorFullFock H)) =
      Set.centralizer (Set.range (tensorFamilyField e)) := by
    ext T
    change T ∈ StarSubalgebra.centralizer ℂ (Set.range (tensorFamilyField e)) ↔ _
    rw [StarSubalgebra.mem_centralizer_iff, Set.mem_centralizer_iff]
    constructor
    · intro h g hg
      exact (h g hg).1
    · intro h g hg
      obtain ⟨i, rfl⟩ := hg
      constructor
      · exact h _ (Set.mem_range_self i)
      · simpa only [ContinuousLinearMap.star_eq_adjoint, ou_tensorFamilyField_adjoint]
          using h _ (Set.mem_range_self i)
  have hd : (StarSubalgebra.centralizer ℂ
      (C : Set (TensorFullFock H →L[ℂ] TensorFullFock H)) :
        Set (TensorFullFock H →L[ℂ] TensorFullFock H)) =
      Set.centralizer (C : Set (TensorFullFock H →L[ℂ] TensorFullFock H)) := by
    rw [StarSubalgebra.coe_centralizer, StarMemClass.star_coe_eq, Set.union_self]
  change (StarSubalgebra.centralizer ℂ
      (C : Set (TensorFullFock H →L[ℂ] TensorFullFock H)) :
        Set (TensorFullFock H →L[ℂ] TensorFullFock H)) = _
  rw [hd, hc]

instance (e : I → H) : IsClosed
    (tensorFamilyDoubleAlgebra e : Set (TensorFullFock H →L[ℂ] TensorFullFock H)) := by
  rw [tensorFamilyDoubleAlgebra_coe]
  exact Set.isClosed_centralizer _

/-- The genuine concrete von Neumann algebra for any prescribed field family. -/
def tensorFamilyVonNeumannAlgebra (e : I → H) : VonNeumannAlgebra (TensorFullFock H) where
  toStarSubalgebra := tensorFamilyDoubleAlgebra e
  centralizer_centralizer' := by
    change (tensorFamilyDoubleAlgebra e : Set (TensorFullFock H →L[ℂ] TensorFullFock H)).centralizer.centralizer =
      (tensorFamilyDoubleAlgebra e : Set (TensorFullFock H →L[ℂ] TensorFullFock H))
    rw [tensorFamilyDoubleAlgebra_coe, Set.centralizer_centralizer_centralizer]

theorem tensorFamilyVonNeumannAlgebra_mem_iff (e : I → H)
    {T : TensorFullFock H →L[ℂ] TensorFullFock H} :
    T ∈ tensorFamilyVonNeumannAlgebra e ↔
      T ∈ Set.centralizer (Set.centralizer (Set.range (tensorFamilyField e))) := by
  change T ∈ (tensorFamilyDoubleAlgebra e : Set (TensorFullFock H →L[ℂ] TensorFullFock H)) ↔ _
  rw [tensorFamilyDoubleAlgebra_coe]

/-- Positive normalized actual vacuum state; faithful trace requires an ON family. -/
def tensorFamilyVonNeumannVacuumState (e : I → H) : StarProbabilitySpace (tensorFamilyDoubleAlgebra e) where
  expectation := (tensorVacuumState H).expectation.comp (tensorFamilyDoubleAlgebra e).val.toLinearMap
  map_one := (tensorVacuumState H).map_one
  map_star T := (tensorVacuumState H).map_star (T : TensorFullFock H →L[ℂ] TensorFullFock H)
  positive T := (tensorVacuumState H).positive (T : TensorFullFock H →L[ℂ] TensorFullFock H)

example (e : I → H) : CStarAlgebra (tensorFamilyDoubleAlgebra e) := inferInstance

end FreeProbability.Fock

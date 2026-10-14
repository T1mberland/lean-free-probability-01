import FreeProbability.Fock.OrnsteinUhlenbeckVonNeumannCyclicRepresentation

/-! Actual ON-family Wick vacuum words in the ORIGINAL complete cyclic Hilbert space. -/
noncomputable section
open scoped Classical InnerProductSpace
namespace FreeProbability.Fock
variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual prescribed-family Wick vacuum vector, with its proved original cyclic codomain. -/
def familyCyclicWord (e : I → H) (w : List I) : familyCyclicSpace e :=
  familyCyclicVector e (familyClosedWick e w)

/-- Adapted full tensor transport identifies the original family creator words, retaining their index order. -/
theorem OrthonormalFamilyExtension.tensorTransport_familyCreatorWord {e : I → H}
    (d : OrthonormalFamilyExtension e) (w : List I) :
    d.tensorTransport (word (w.map d.index)) = tensorCreatorWord (w.map e) (tensorVacuum H) := by
  induction w with
  | nil => exact d.tensorTransport_vacuum
  | cons i w ih =>
    rw [List.map_cons, ← creation_word, ← d.creation_family i, d.tensorTransport_creation, ih]
    rfl

/-- The cyclic word is the actual transported canonical word of the adapted ON-family model. -/
theorem familyCyclicWord_transport {e : I → H} (d : OrthonormalFamilyExtension e) (w : List I) :
    (familyCyclicWord e w : TensorFullFock H) = d.tensorTransport (word (w.map d.index)) := by
  change tensorVectorWick (w.map e) (tensorVacuum H) = _
  rw [tensorVectorWick_vacuum_creator]
  exact (d.tensorTransport_familyCreatorWord w).symm

/-- Exact Gram identity for the genuine family cyclic words, with arbitrary index cardinality. -/
theorem familyCyclicWord_inner (e : I → H) (he : Orthonormal ℂ e) (u v : List I) :
    inner ℂ (familyCyclicWord e u) (familyCyclicWord e v) = if u = v then 1 else 0 := by
  let d := orthonormalFamilyExtension he
  change inner ℂ (familyCyclicWord e u : TensorFullFock H) (familyCyclicWord e v : TensorFullFock H) = _
  rw [familyCyclicWord_transport d, familyCyclicWord_transport d, d.tensorTransport.inner_map_map, inner_word]
  simp only [(List.map_injective_iff.mpr d.index_injective).eq_iff]

 theorem familyCyclicWord_orthonormal (e : I → H) (he : Orthonormal ℂ e) :
    Orthonormal ℂ (familyCyclicWord e) := by
  rw [orthonormal_iff_ite]
  exact familyCyclicWord_inner e he

end FreeProbability.Fock

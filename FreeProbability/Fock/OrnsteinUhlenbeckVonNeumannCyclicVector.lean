import FreeProbability.Fock.OrnsteinUhlenbeckVonNeumannCyclicProjection

/-! Every actual family double-commutant vacuum vector belongs to the original complete cyclic space. -/
noncomputable section
open scoped Classical InnerProductSpace
namespace FreeProbability.Fock
variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every element of the literal double commutant sends the vacuum into the ORIGINAL family cyclic space.
The field family is arbitrary, with no spanning or orthonormality assumption. -/
theorem ouVonNeumann_vacuum_mem_cyclic (e : I → H) (T : tensorFamilyDoubleAlgebra e) :
    (T : TensorFullFock H →L[ℂ] TensorFullFock H) (tensorVacuum H) ∈ familyCyclicSpace e := by
  apply (familyCyclicSpace e).starProjection_eq_self_iff.mp
  change ouFamilyCyclicProjection e
    ((T : TensorFullFock H →L[ℂ] TensorFullFock H) (tensorVacuum H)) = _
  have hT : (T : TensorFullFock H →L[ℂ] TensorFullFock H) ∈
      Set.centralizer (Set.centralizer (Set.range (tensorFamilyField e))) := by
    rw [← tensorFamilyDoubleAlgebra_coe]
    exact T.property
  have hc := (Set.mem_centralizer_iff.mp hT) (ouFamilyCyclicProjection e)
    (ouFamilyCyclicProjection_mem_commutant e)
  have he := DFunLike.congr_fun hc (tensorVacuum H)
  simpa only [mul_apply_eq_comp, ouFamilyCyclicProjection_vacuum] using he

/-- The original norm-closed given-family algebra embeds in its actual literal double commutant. -/
theorem ouCyclic_native_le_double (e : I → H) : tensorFamilyAlgebra e ≤ tensorFamilyDoubleAlgebra e := by
  have hp : StarAlgebra.adjoin ℂ (Set.range (tensorFamilyField e)) ≤ tensorFamilyDoubleAlgebra e := by
    apply StarAlgebra.adjoin_le
    intro T hT
    rw [tensorFamilyDoubleAlgebra_coe]
    exact Set.subset_centralizer_centralizer hT
  exact StarSubalgebra.topologicalClosure_minimal hp inferInstance

/-- Actual inclusion preserving the literal bounded operator. -/
def ouCyclicNativeInclusion (e : I → H) : tensorFamilyAlgebra e →⋆ₐ[ℂ] tensorFamilyDoubleAlgebra e :=
  StarSubalgebra.inclusion (ouCyclic_native_le_double e)

/-- Genuine bounded vacuum evaluation with the ORIGINAL complete cyclic Hilbert codomain. -/
def ouVonNeumannCyclicVector (e : I → H) : tensorFamilyDoubleAlgebra e →L[ℂ] familyCyclicSpace e :=
  (ouVonNeumannVacuumVector e).codRestrict (familyCyclicSpace e) (ouVonNeumann_vacuum_mem_cyclic e)

@[simp] theorem ouVonNeumannCyclicVector_coe (e : I → H) (T : tensorFamilyDoubleAlgebra e) :
    (ouVonNeumannCyclicVector e T : TensorFullFock H) =
      (T : TensorFullFock H →L[ℂ] TensorFullFock H) (tensorVacuum H) := rfl

@[simp] theorem ouVonNeumannCyclicVector_native (e : I → H) (T : tensorFamilyAlgebra e) :
    ouVonNeumannCyclicVector e (ouCyclicNativeInclusion e T) = familyCyclicVector e T := rfl

/-- Whole-double-commutant vacuum evaluation has genuinely dense range in that SAME cyclic Hilbert space. -/
theorem ouVonNeumannCyclicVector_denseRange (e : I → H) : DenseRange (ouVonNeumannCyclicVector e) := by
  apply (familyCyclicVector_denseRange e).mono
  rintro _ ⟨T, rfl⟩
  exact ⟨ouCyclicNativeInclusion e T, rfl⟩

/-- For an ON family the actual whole-algebra cyclic representation is injective. -/
theorem ouVonNeumannCyclicVector_injective (e : I → H) (he : Orthonormal ℂ e) :
    Function.Injective (ouVonNeumannCyclicVector e) := by
  intro T S h
  apply ouVonNeumannVacuumVector_injective e he
  exact congrArg Subtype.val h

/-- The original complete cyclic OU contraction agrees on EVERY whole-double-commutant vacuum vector. -/
theorem familyOUL2_ouVonNeumannCyclicVector (e : I → H) (he : Orthonormal ℂ e)
    (t : ℝ) (ht : 0 ≤ t) (T : tensorFamilyDoubleAlgebra e) :
    familyOUL2 e he t ht (ouVonNeumannCyclicVector e T) =
      ouVonNeumannCyclicVector e (ouVonNeumannTimeCP e t ht T) := by
  apply Subtype.ext
  exact (ouVonNeumannTimeCP_vacuum_vector e t ht T).symm

end FreeProbability.Fock

import FreeProbability.Fock.OrnsteinUhlenbeckFamilyCyclicBasisOperators

/-! # Exact native norm-closed image of the family word representation

Only the original C-star family algebra is identified with the closed word
algebra. No surjectivity of the entire double-commutant representation is asserted.
-/
noncomputable section
open scoped Classical
namespace FreeProbability.Fock
variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Restriction of the actual cyclic representation to the original native algebra. -/
def familyNativeWordRepresentation (e : I → H) (he : Orthonormal ℂ e) :
    tensorFamilyAlgebra e →⋆ₐ[ℂ] (WordSpace I →L[ℂ] WordSpace I) :=
  (familyWordRepresentation e he).comp (ouCyclicNativeInclusion e)

@[simp] theorem familyNativeWordRepresentation_Wick (e : I → H) (he : Orthonormal ℂ e)
    (w : List I) : familyNativeWordRepresentation e he (familyClosedWick e w) = wick w :=
  familyWordRepresentation_Wick e he w

@[simp] theorem familyNativeWordRepresentation_field (e : I → H) (he : Orthonormal ℂ e)
    (i : I) : familyNativeWordRepresentation e he (ouCyclicNativeField e i) = semicircular i :=
  familyWordRepresentation_field e he i

theorem familyNativeWordRepresentation_injective (e : I → H) (he : Orthonormal ℂ e) :
    Function.Injective (familyNativeWordRepresentation e he) := by
  intro T S h
  apply Subtype.ext
  have hh := familyWordRepresentation_injective e he h
  exact congrArg (fun A : tensorFamilyDoubleAlgebra e =>
    (A : TensorFullFock H →L[ℂ] TensorFullFock H)) hh

theorem familyNativeWordRepresentation_isometry (e : I → H) (he : Orthonormal ℂ e) :
    Isometry (familyNativeWordRepresentation e he) :=
  NonUnitalStarAlgHom.isometry _ (familyNativeWordRepresentation_injective e he)

/-- The entire native image lies in the canonical word norm closure. -/
theorem familyNativeWordRepresentation_mem (e : I → H) (he : Orthonormal ℂ e)
    (T : tensorFamilyAlgebra e) :
    familyNativeWordRepresentation e he T ∈ closedSemicircularAlgebra I := by
  let φ := familyNativeWordRepresentation e he
  let S := ((closedSemicircularAlgebra I).toSubmodule.comap φ.toLinearMap).map
    (tensorFamilyAlgebra e).val.toLinearMap
  have hs : familyWickSpan e ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w, rfl⟩
    apply Submodule.mem_map.mpr
    refine ⟨familyClosedWick e w, ?_, rfl⟩
    change φ (familyClosedWick e w) ∈ closedSemicircularAlgebra I
    rw [familyNativeWordRepresentation_Wick]
    exact (semicircularAlgebra I).le_topologicalClosure (wick_mem_algebra w)
  let P := StarAlgebra.adjoin ℂ (Set.range (tensorFamilyField e))
  let j : P → tensorFamilyAlgebra e := StarSubalgebra.inclusion P.le_topologicalClosure
  have hd : DenseRange j := by
    change DenseRange (Set.inclusion P.le_topologicalClosure)
    exact (denseRange_inclusion_iff P.le_topologicalClosure).mpr Set.Subset.rfl
  have hp : ∀ A : P, φ (j A) ∈ closedSemicircularAlgebra I := by
    intro A
    obtain ⟨U, hU, hv⟩ := Submodule.mem_map.mp
      (hs (family_polynomial_mem_WickSpan e A.property))
    have hu : U = j A := Subtype.ext hv
    change φ U ∈ closedSemicircularAlgebra I at hU
    rw [hu] at hU
    exact hU
  exact hd.induction_on (p := fun A => φ A ∈ closedSemicircularAlgebra I) T
    ((StarSubalgebra.isClosed_topologicalClosure (semicircularAlgebra I)).preimage
      (familyNativeWordRepresentation_isometry e he).continuous) hp

/-- Completeness and injective C-star isometry make the native image closed. -/
theorem familyNativeWordRepresentation_closed_range (e : I → H) (he : Orthonormal ℂ e) :
    IsClosed (Set.range (familyNativeWordRepresentation e he)) :=
  (familyNativeWordRepresentation_isometry e he).isClosedEmbedding.isClosed_range

/-- Exact equality with the canonical closed semicircular word algebra. -/
theorem familyNativeWordRepresentation_range (e : I → H) (he : Orthonormal ℂ e) :
    (familyNativeWordRepresentation e he).range = closedSemicircularAlgebra I := by
  apply le_antisymm
  · rintro _ ⟨T, rfl⟩
    exact familyNativeWordRepresentation_mem e he T
  · apply StarSubalgebra.topologicalClosure_minimal
    · apply StarAlgebra.adjoin_le
      rintro _ ⟨i, rfl⟩
      exact ⟨ouCyclicNativeField e i, familyNativeWordRepresentation_field e he i⟩
    · exact familyNativeWordRepresentation_closed_range e he

end FreeProbability.Fock

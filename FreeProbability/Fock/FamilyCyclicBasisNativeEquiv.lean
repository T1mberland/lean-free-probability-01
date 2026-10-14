import FreeProbability.Fock.FamilyCyclicBasisNativeImage

/-! # Isometric native transport and the exact closed-word membership criterion -/
noncomputable section
open scoped Classical
namespace FreeProbability.Fock
variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Actual native representation with its proved closed-word codomain. -/
def familyNativeWordHom (e : I → H) (he : Orthonormal ℂ e) :
    tensorFamilyAlgebra e →⋆ₐ[ℂ] closedSemicircularAlgebra I :=
  (familyNativeWordRepresentation e he).codRestrict _ (familyNativeWordRepresentation_mem e he)

theorem familyNativeWordHom_bijective (e : I → H) (he : Orthonormal ℂ e) :
    Function.Bijective (familyNativeWordHom e he) := by
  constructor
  · intro T S h
    apply familyNativeWordRepresentation_injective e he
    exact congrArg Subtype.val h
  · intro A
    have hm : (A : WordSpace I →L[ℂ] WordSpace I) ∈ (familyNativeWordRepresentation e he).range := by
      rw [familyNativeWordRepresentation_range]
      exact A.property
    obtain ⟨T, ht⟩ := hm
    exact ⟨T, Subtype.ext ht⟩

/-- Genuine isometric star-algebra equivalence of the original two norm closures. -/
def familyNativeWordEquiv (e : I → H) (he : Orthonormal ℂ e) :
    tensorFamilyAlgebra e ≃⋆ₐ[ℂ] closedSemicircularAlgebra I :=
  StarAlgEquiv.ofBijective (familyNativeWordHom e he) (familyNativeWordHom_bijective e he)

@[simp] theorem familyNativeWordEquiv_coe (e : I → H) (he : Orthonormal ℂ e)
    (T : tensorFamilyAlgebra e) :
    (familyNativeWordEquiv e he T : WordSpace I →L[ℂ] WordSpace I) =
      familyWordRepresentation e he (ouCyclicNativeInclusion e T) := rfl

@[simp] theorem familyNativeWordEquiv_norm (e : I → H) (he : Orthonormal ℂ e)
    (T : tensorFamilyAlgebra e) : ‖familyNativeWordEquiv e he T‖ = ‖T‖ :=
  by
    change ‖familyNativeWordRepresentation e he T‖ = ‖T‖
    exact NonUnitalStarAlgHom.norm_map (familyNativeWordRepresentation e he)
      (familyNativeWordRepresentation_injective e he) T

/-- Every closed word operator has its actual unique native preimage. -/
@[simp] theorem familyNativeWordEquiv_preimage (e : I → H) (he : Orthonormal ℂ e)
    (A : closedSemicircularAlgebra I) :
    familyWordRepresentation e he
      (ouCyclicNativeInclusion e ((familyNativeWordEquiv e he).symm A)) =
        (A : WordSpace I →L[ℂ] WordSpace I) := by
  exact congrArg Subtype.val ((familyNativeWordEquiv e he).apply_symm_apply A)

/-- Closed-word membership detects exactly the native part of the double commutant. -/
theorem familyWordRepresentation_mem_closed_iff (e : I → H) (he : Orthonormal ℂ e)
    (T : tensorFamilyDoubleAlgebra e) :
    familyWordRepresentation e he T ∈ closedSemicircularAlgebra I ↔
      (T : TensorFullFock H →L[ℂ] TensorFullFock H) ∈ tensorFamilyAlgebra e := by
  constructor
  · intro hT
    let A : closedSemicircularAlgebra I := ⟨familyWordRepresentation e he T, hT⟩
    let S := (familyNativeWordEquiv e he).symm A
    have hs : ouCyclicNativeInclusion e S = T :=
      familyWordRepresentation_injective e he (familyNativeWordEquiv_preimage e he A)
    have hh := S.property
    have hv := congrArg (fun U : tensorFamilyDoubleAlgebra e =>
      (U : TensorFullFock H →L[ℂ] TensorFullFock H)) hs
    change (S : TensorFullFock H →L[ℂ] TensorFullFock H) = _ at hv
    rwa [hv] at hh
  · intro hT
    let S : tensorFamilyAlgebra e := ⟨T, hT⟩
    exact familyNativeWordRepresentation_mem e he S

end FreeProbability.Fock

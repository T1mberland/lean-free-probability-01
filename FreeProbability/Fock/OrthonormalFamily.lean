import FreeProbability.Fock.BasisTensorLevels
import FreeProbability.Fock.FreeCStarModel

/-!
# Complete Fock models adapted to arbitrary orthonormal families

An orthonormal family need not span the original Hilbert space. We extend its
range to an actual Hilbert basis, and use the complete Fock model of that basis.
The original vectors act by genuine bounded creation operators; their fields
are an injectively selected canonical free family. This construction does not
identify an independently chosen basis model with the adapted model.
-/

noncomputable section
open scoped Classical InnerProductSpace TensorProduct
open UniformSpace

namespace FreeProbability.Fock

variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {e : I → H}

/-- A complete Hilbert basis retaining all members of the prescribed family. -/
structure OrthonormalFamilyExtension (e : I → H) where
  indices : Set H
  basis : HilbertBasis indices ℂ H
  index : I → indices
  index_injective : Function.Injective index
  basis_index : ∀ i, basis (index i) = e i

/-- No totality or countability hypothesis is required on the orthonormal family. -/
theorem exists_orthonormalFamilyExtension (he : Orthonormal ℂ e) :
    Nonempty (OrthonormalFamilyExtension e) := by
  obtain ⟨w, b, hw, hb⟩ := he.toSubtypeRange.exists_hilbertBasis_extension
  let j : I → w := fun i => ⟨e i, hw ⟨i, rfl⟩⟩
  refine ⟨⟨w, b, j, ?_, ?_⟩⟩
  · intro i k h
    exact he.linearIndependent.injective (congrArg Subtype.val h)
  · intro i
    rw [hb]

/-- A selected extension, supplied by the actual Hilbert-basis extension theorem. -/
def orthonormalFamilyExtension (he : Orthonormal ℂ e) : OrthonormalFamilyExtension e :=
  Classical.choice (exists_orthonormalFamilyExtension he)

omit [CompleteSpace H]

namespace OrthonormalFamilyExtension

variable (d : OrthonormalFamilyExtension e)

/-- The adapted model is a complete square-summable full word Fock space. -/
abbrev Space := BasisFockSpace d.basis

example : CompleteSpace d.Space := inferInstance

/-- Creation by any vector of the original space in the adapted complete model. -/
def creation (h : H) : d.Space →L[ℂ] d.Space := basisCreation d.basis h

/-- The genuine Hilbert adjoint of creation. -/
def annihilation (h : H) : d.Space →L[ℂ] d.Space := basisAnnihilation d.basis h

@[simp] theorem norm_creation (h : H) : ‖d.creation h‖ = ‖h‖ :=
  norm_basisCreation d.basis h

@[simp] theorem norm_annihilation (h : H) : ‖d.annihilation h‖ = ‖h‖ :=
  norm_basisAnnihilation d.basis h

theorem annihilation_creation (h k : H) :
    d.annihilation h * d.creation k = inner ℂ h k • (1 : d.Space →L[ℂ] d.Space) :=
  basisAnnihilation_creation d.basis h k

@[simp] theorem creation_family (i : I) :
    d.creation (e i) = Fock.creation (d.index i) := by
  change basisCreation d.basis (e i) = _
  rw [← d.basis_index i, basisCreation_basis]

@[simp] theorem annihilation_family (i : I) :
    d.annihilation (e i) = Fock.annihilation (d.index i) := by
  change (d.creation (e i)).adjoint = _
  rw [d.creation_family]
  rfl

/-- The adapted model has an actual complete Hilbert direct-sum grading. -/
def grading : d.Space ≃ₗᵢ[ℂ] GradedWordSpace d.indices := lengthDecomposition

/-- Its successive levels are genuine completed tensor products with the original space. -/
def successorTensorEquiv (n : ℕ) :
    Completion (H ⊗[ℂ] WordLevel d.indices n) ≃ₗᵢ[ℂ] WordLevel d.indices (n + 1) :=
  basisSuccessorLevelTensorEquiv d.basis n

/-- Creation literally tensors by the original vector on the complete graded levels. -/
theorem tensor_creation (n : ℕ) (h : H) (f : WordLevel d.indices n) :
    levelEmbedding (n + 1) (d.successorTensorEquiv n
      ((h ⊗ₜ[ℂ] f : H ⊗[ℂ] WordLevel d.indices n) :
        Completion (H ⊗[ℂ] WordLevel d.indices n))) =
      d.creation h (levelEmbedding n f) :=
  basisLevelEmbedding_tensorCreation d.basis n h f

/-- The field associated to a member of the original orthonormal family. -/
def field (i : I) : d.Space →L[ℂ] d.Space := d.creation (e i) + d.annihilation (e i)

@[simp] theorem field_eq_semicircular (i : I) :
    d.field i = semicircular (d.index i) := by
  simp [field, semicircular]

@[simp] theorem norm_field (i : I) : ‖d.field i‖ = 2 := by
  rw [d.field_eq_semicircular, norm_semicircular]

theorem isSelfAdjoint_field (i : I) : IsSelfAdjoint (d.field i) := by
  rw [d.field_eq_semicircular]
  exact isSelfAdjoint_semicircular _

/-- The actual fields lie in the faithful tracial closed C-star model of the extension. -/
def closedField (i : I) : closedSemicircularAlgebra d.indices :=
  closedSemicircular (d.index i)

@[simp] theorem coe_closedField (i : I) :
    (d.closedField i : d.Space →L[ℂ] d.Space) = d.field i :=
  (d.field_eq_semicircular i).symm

/-- Selecting the original family preserves actual closed-algebra freeness. -/
theorem freelyIndependent :
    FreelyIndependent (closedGeneratedVacuumState d.indices).toProbabilitySpace
      (fun i => closedGeneratorAlgebra (d.index i)) :=
  (freelyIndependent_closedGeneratedVacuumState d.indices).reindex d.index d.index_injective

end OrthonormalFamilyExtension
end FreeProbability.Fock

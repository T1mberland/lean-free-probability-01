import FreeProbability.Fock.BasisTensorLevels

/-!
# A genuine full Fock space for every complex Hilbert space

A Hilbert basis exists for every complete complex inner-product space. Choosing
one realizes full Fock space as complete square-summable word amplitudes, with
an exact Hilbert grading, scalar vacuum level, and completed tensor recursion.
Creation by arbitrary original vectors is bounded and agrees with tensoring on
each level. The canonical orthonormal generators inherit the previously proved
free semicircular laws; traciality is not claimed for all complex-vector fields.
-/

noncomputable section
open scoped Classical InnerProductSpace TensorProduct
open UniformSpace

namespace FreeProbability.Fock

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The index set of a chosen genuine Hilbert basis of the original space. -/
def fullFockBasisSet : Set H := Classical.choose (exists_hilbertBasis ℂ H)

/-- An actual Hilbert basis, obtained from the existence theorem without additional assumptions. -/
def fullFockBasis : HilbertBasis (fullFockBasisSet H) ℂ H :=
  Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ H))

/-- Genuine complete full Fock space of the original complex Hilbert space. -/
abbrev FullFock := WordSpace (fullFockBasisSet H)

/-- The complete tensor levels, realized as word amplitudes in the chosen basis. -/
abbrev FullFockLevel (n : ℕ) := WordLevel (fullFockBasisSet H) n

/-- The unit vacuum in full Fock space. -/
def fullVacuum : FullFock H := vacuum

@[simp] theorem norm_fullVacuum : ‖fullVacuum H‖ = 1 := norm_vacuum

/-- Actual bounded creation by an arbitrary original Hilbert-space vector. -/
def fullCreation (h : H) : FullFock H →L[ℂ] FullFock H := basisCreation (fullFockBasis H) h

/-- Actual Hilbert adjoint of full creation. -/
def fullAnnihilation (h : H) : FullFock H →L[ℂ] FullFock H := (fullCreation H h).adjoint

@[simp] theorem norm_fullCreation (h : H) : ‖fullCreation H h‖ = ‖h‖ :=
  norm_basisCreation (fullFockBasis H) h

@[simp] theorem norm_fullAnnihilation (h : H) : ‖fullAnnihilation H h‖ = ‖h‖ :=
  norm_basisAnnihilation (fullFockBasis H) h

/-- Canonical creation-annihilation relation in the original Hilbert space. -/
theorem fullAnnihilation_creation (h k : H) :
    fullAnnihilation H h * fullCreation H k =
      inner ℂ h k • (1 : FullFock H →L[ℂ] FullFock H) :=
  basisAnnihilation_creation (fullFockBasis H) h k

@[simp] theorem fullAnnihilation_vacuum (h : H) :
    fullAnnihilation H h (fullVacuum H) = 0 :=
  basisAnnihilation_vacuum (fullFockBasis H) h

/-- The whole Fock space is the genuine Hilbert sum of its completed tensor levels. -/
def fullFockGrading : FullFock H ≃ₗᵢ[ℂ] lp (fun n => ↥(FullFockLevel H n)) 2 :=
  lengthDecomposition

/-- The vacuum tensor level is isometrically the scalar Hilbert space. -/
def fullFockScalarLevel : ℂ ≃ₗᵢ[ℂ] FullFockLevel H 0 := scalarLevelEquiv

/-- Exact completed tensor recursion, with the original Hilbert space as first factor. -/
def fullFockTensorLevel (n : ℕ) :
    Completion (H ⊗[ℂ] FullFockLevel H n) ≃ₗᵢ[ℂ] FullFockLevel H (n + 1) :=
  basisSuccessorLevelTensorEquiv (fullFockBasis H) n

/-- Creation is literal tensoring by the original vector on every complete tensor level. -/
theorem fullCreation_tensorLevel (n : ℕ) (h : H) (f : FullFockLevel H n) :
    levelEmbedding (n + 1) (fullFockTensorLevel H n
      ((h ⊗ₜ[ℂ] f : H ⊗[ℂ] FullFockLevel H n) : Completion (H ⊗[ℂ] FullFockLevel H n))) =
      fullCreation H h (levelEmbedding n f) :=
  basisLevelEmbedding_tensorCreation (fullFockBasis H) n h f

end FreeProbability.Fock

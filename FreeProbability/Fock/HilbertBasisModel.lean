import FreeProbability.Fock.VectorCreation

/-!
# Creation for an arbitrary Hilbert space with a chosen Hilbert basis

Transport through the actual Hilbert-basis isometry gives bounded creation and
annihilation for every vector of a complex Hilbert space. The underlying Fock
space is the completed word space on the basis indices. Identification with the
Hilbert direct sum of completed tensor powers remains a separate obligation.
No traciality assertion is made for the family indexed by all complex vectors.
-/

noncomputable section
open scoped Classical InnerProductSpace

namespace FreeProbability.Fock

variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A genuine complete Fock model associated to a chosen Hilbert basis. -/
abbrev BasisFockSpace (_b : HilbertBasis I ℂ H) := WordSpace I

/-- Bounded creation by any vector of the given Hilbert space. -/
def basisCreation (b : HilbertBasis I ℂ H) (h : H) :
    BasisFockSpace b →L[ℂ] BasisFockSpace b := vectorCreation (b.repr h)

/-- Actual Hilbert adjoint of creation in the transported model. -/
def basisAnnihilation (b : HilbertBasis I ℂ H) (h : H) :
    BasisFockSpace b →L[ℂ] BasisFockSpace b := (basisCreation b h).adjoint

@[simp] theorem norm_basisCreation (b : HilbertBasis I ℂ H) (h : H) :
    ‖basisCreation b h‖ = ‖h‖ := by simp [basisCreation]

@[simp] theorem norm_basisAnnihilation (b : HilbertBasis I ℂ H) (h : H) :
    ‖basisAnnihilation b h‖ = ‖h‖ := by
  rw [basisAnnihilation, ContinuousLinearMap.adjoint.norm_map, norm_basisCreation]

/-- The canonical creation-annihilation relation uses the original Hilbert inner product. -/
theorem basisAnnihilation_creation (b : HilbertBasis I ℂ H) (h k : H) :
    basisAnnihilation b h * basisCreation b k =
      inner ℂ h k • (1 : BasisFockSpace b →L[ℂ] BasisFockSpace b) := by
  change vectorAnnihilation (b.repr h) * vectorCreation (b.repr k) = _
  rw [vectorAnnihilation_creation, b.repr.inner_map_map]

/-- Every Hilbert-space vector annihilates the vacuum. -/
@[simp] theorem basisAnnihilation_vacuum (b : HilbertBasis I ℂ H) (h : H) :
    basisAnnihilation b h (vacuum : BasisFockSpace b) = 0 :=
  vectorAnnihilation_vacuum (b.repr h)

/-- Creation embeds the original Hilbert space linearly and isometrically into operators. -/
def basisCreationIsometry (b : HilbertBasis I ℂ H) :
    H →ₗᵢ[ℂ] (BasisFockSpace b →L[ℂ] BasisFockSpace b) :=
  vectorCreationIsometry.comp b.repr.toLinearIsometry

/-- The original Hilbert space embeds as the one-particle sector of this Fock model. -/
def basisOneParticleEmbedding (b : HilbertBasis I ℂ H) : H →ₗᵢ[ℂ] BasisFockSpace b :=
  oneParticleEmbedding.comp b.repr.toLinearIsometry

/-- Chosen basis vectors give exactly the canonical word creation operators. -/
@[simp] theorem basisCreation_basis (b : HilbertBasis I ℂ H) (i : I) :
    basisCreation b (b i) = creation i := by
  rw [basisCreation, b.repr_self, vectorCreation_single]

@[simp] theorem basisOneParticleEmbedding_basis (b : HilbertBasis I ℂ H) (i : I) :
    basisOneParticleEmbedding b (b i) = word [i] := by
  change oneParticleEmbedding (b.repr (b i)) = _
  rw [b.repr_self, oneParticleEmbedding_single]

end FreeProbability.Fock

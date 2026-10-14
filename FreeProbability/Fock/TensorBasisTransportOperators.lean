import FreeProbability.Fock.TensorBasisTransport
import FreeProbability.Fock.TensorSemicircular

/-! # Actual creation, adjoint, field, and vacuum transport into fixed tensor Fock space -/
noncomputable section
open scoped InnerProductSpace
namespace FreeProbability.Fock.OrthonormalFamilyExtension
variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {e : I → H} (d : OrthonormalFamilyExtension e)

/-- Actual unitary star-algebra equivalence on full bounded-operator algebras. -/
def tensorOperatorTransport : (d.Space →L[ℂ] d.Space) ≃⋆ₐ[ℂ]
    (TensorFullFock H →L[ℂ] TensorFullFock H) := d.tensorTransport.conjStarAlgEquiv

@[simp] theorem tensorOperatorTransport_creation (h : H) :
    d.tensorOperatorTransport (d.creation h) = tensorCreation H h := by
  apply ContinuousLinearMap.ext
  intro f
  change d.tensorTransport (d.creation h (d.tensorTransport.symm f)) = _
  rw [d.tensorTransport_creation, d.tensorTransport.apply_symm_apply]

@[simp] theorem tensorOperatorTransport_annihilation (h : H) :
    d.tensorOperatorTransport (d.annihilation h) = tensorAnnihilation H h := by
  change d.tensorOperatorTransport (star (d.creation h)) = star (tensorCreation H h)
  rw [map_star, d.tensorOperatorTransport_creation]

@[simp] theorem tensorOperatorTransport_field (i : I) :
    d.tensorOperatorTransport (d.field i) = tensorCreation H (e i) + tensorAnnihilation H (e i) := by
  rw [field, map_add, d.tensorOperatorTransport_creation, d.tensorOperatorTransport_annihilation]

/-- Vacuum expectation is transported by the actual vacuum-fixing full-space unitary. -/
theorem tensorOperatorTransport_expectation (T : d.Space →L[ℂ] d.Space) :
    (tensorVacuumState H).expectation (d.tensorOperatorTransport T) = vacuumExpectation T := by
  rw [tensorVacuumState_expectation]
  have hv : d.tensorTransport.symm (tensorVacuum H) = d.vacuum := by
    apply d.tensorTransport.injective
    rw [d.tensorTransport.apply_symm_apply, d.tensorTransport_vacuum]
  change inner ℂ (tensorVacuum H) (d.tensorTransport (T (d.tensorTransport.symm (tensorVacuum H)))) = _
  rw [hv, ← d.tensorTransport_vacuum]
  exact d.tensorTransport.inner_map_map d.vacuum (T d.vacuum)

/-- Reverse transport preserves actual vacuum expectation as well. -/
theorem tensorOperatorTransport_symm_expectation
    (T : TensorFullFock H →L[ℂ] TensorFullFock H) :
    vacuumExpectation (d.tensorOperatorTransport.symm T) = (tensorVacuumState H).expectation T := by
  have he := d.tensorOperatorTransport_expectation (d.tensorOperatorTransport.symm T)
  rw [StarAlgEquiv.apply_symm_apply] at he
  exact he.symm

end FreeProbability.Fock.OrthonormalFamilyExtension

import FreeProbability.Fock.TensorFamilyFaithfulness
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-! # The actual generated-algebra equivalence between adapted and fixed tensor models -/
noncomputable section
namespace FreeProbability.Fock
variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Literal generator in the norm-closed prescribed-family algebra on fixed tensor Fock space. -/
def tensorFamilyGenerator (e : I → H) (i : I) : tensorFamilyAlgebra e :=
  ⟨tensorFamilyField e i, (StarAlgebra.adjoin ℂ (Set.range (tensorFamilyField e))).le_topologicalClosure
    (StarAlgebra.subset_adjoin ℂ _ ⟨i, rfl⟩)⟩

namespace OrthonormalFamilyExtension
variable {e : I → H} (d : OrthonormalFamilyExtension e)

/-- Actual onto star-algebra equivalence of both literal generated norm closures. -/
def tensorGeneratedEquiv : d.generatedAlgebra ≃⋆ₐ[ℂ] tensorFamilyAlgebra e where
  toFun T := ⟨d.tensorOperatorTransport T, d.generatedAlgebra_maps_into_tensorFamily T.property⟩
  invFun T := ⟨d.tensorOperatorTransport.symm T, d.tensorFamilyAlgebra_maps_into T.property⟩
  left_inv T := Subtype.ext (d.tensorOperatorTransport.symm_apply_apply T)
  right_inv T := Subtype.ext (d.tensorOperatorTransport.apply_symm_apply T)
  map_mul' T S := Subtype.ext (map_mul d.tensorOperatorTransport (T : d.Space →L[ℂ] d.Space) (S : d.Space →L[ℂ] d.Space))
  map_add' T S := Subtype.ext (map_add d.tensorOperatorTransport (T : d.Space →L[ℂ] d.Space) (S : d.Space →L[ℂ] d.Space))
  map_smul' c T := Subtype.ext (map_smul d.tensorOperatorTransport.toAlgEquiv.toAlgHom c (T : d.Space →L[ℂ] d.Space))
  map_star' T := Subtype.ext (map_star d.tensorOperatorTransport (T : d.Space →L[ℂ] d.Space))

/-- The equivalence sends the literal prescribed generator to the same original Hilbert vector field. -/
@[simp] theorem tensorGeneratedEquiv_generator (i : I) :
    d.tensorGeneratedEquiv (d.generator i) = tensorFamilyGenerator e i :=
  Subtype.ext (d.tensorOperatorTransport_field i)

/-- Actual positive vacuum states correspond under the restricted algebra equivalence. -/
theorem tensorGeneratedEquiv_expectation (T : d.generatedAlgebra) :
    (tensorFamilyVacuumState e).expectation (d.tensorGeneratedEquiv T) = d.state.expectation T :=
  d.tensorOperatorTransport_expectation T

/-- Both literal C-star models have identical operator norm under the genuine equivalence. -/
@[simp] theorem tensorGeneratedEquiv_norm (T : d.generatedAlgebra) :
    ‖d.tensorGeneratedEquiv T‖ = ‖T‖ := StarAlgEquiv.norm_map d.tensorGeneratedEquiv T

end OrthonormalFamilyExtension
end FreeProbability.Fock

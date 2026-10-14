import FreeProbability.Fock.OrnsteinUhlenbeckFamilyCyclicBasisWords

/-! A genuine Hilbert basis and completed word unitary for the ORIGINAL family cyclic Hilbert space. -/
noncomputable section
open scoped Classical InnerProductSpace
namespace FreeProbability.Fock
variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Native Wick norm-span totality implies actual cyclic-word Hilbert totality, for any family. -/
theorem familyCyclicWord_orthogonal_eq_bot (e : I → H) :
    (Submodule.span ℂ (Set.range (familyCyclicWord e))).orthogonal = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro f hf
  have hF : (innerSL ℂ f).comp (familyCyclicVector e) = 0 := by
    apply familyContinuousLinearMap_ext_Wick_target e
    intro w
    change inner ℂ f (familyCyclicWord e w) = 0
    exact inner_eq_zero_symm.mp (hf _ (Submodule.subset_span (Set.mem_range_self w)))
  have hi : innerSL ℂ f = 0 := by
    apply DFunLike.ext'
    apply Continuous.ext_on (familyCyclicVector_denseRange e) (innerSL ℂ f).continuous continuous_zero
    rintro _ ⟨T, rfl⟩
    exact DFunLike.congr_fun hF T
  have hh := DFunLike.congr_fun hi f
  exact inner_self_eq_zero.mp hh

/-- Actual Hilbert basis of the ORIGINAL complete cyclic space, indexed by the original family words. -/
def familyCyclicBasis (e : I → H) (he : Orthonormal ℂ e) :
    HilbertBasis (List I) ℂ (familyCyclicSpace e) :=
  HilbertBasis.mkOfOrthogonalEqBot (familyCyclicWord_orthonormal e he) (familyCyclicWord_orthogonal_eq_bot e)

@[simp] theorem familyCyclicBasis_apply (e : I → H) (he : Orthonormal ℂ e) (w : List I) :
    familyCyclicBasis e he w = familyCyclicWord e w := by
  simp only [familyCyclicBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]

/-- Onto Hilbert unitary from completed original-index word Fock space to the ORIGINAL family cyclic space. -/
def familyCyclicWordUnitary (e : I → H) (he : Orthonormal ℂ e) :
    WordSpace I ≃ₗᵢ[ℂ] familyCyclicSpace e := (familyCyclicBasis e he).repr.symm

@[simp] theorem familyCyclicWordUnitary_word (e : I → H) (he : Orthonormal ℂ e) (w : List I) :
    familyCyclicWordUnitary e he (word w) = familyCyclicWord e w := by
  change (familyCyclicBasis e he).repr.symm (word w) = _
  simpa only [word, familyCyclicBasis_apply] using (familyCyclicBasis e he).repr_symm_single w

@[simp] theorem familyCyclicWord_nil (e : I → H) : familyCyclicWord e [] = familyCyclicVacuum e := rfl

@[simp] theorem familyCyclicWordUnitary_vacuum (e : I → H) (he : Orthonormal ℂ e) :
    familyCyclicWordUnitary e he vacuum = familyCyclicVacuum e := by
  exact (familyCyclicWordUnitary_word e he []).trans (familyCyclicWord_nil e)

/-- Every vector in the ORIGINAL complete cyclic space has its genuine unconditional word expansion. -/
theorem hasSum_familyCyclicWord (e : I → H) (he : Orthonormal ℂ e) (f : familyCyclicSpace e) :
    HasSum (fun w => (familyCyclicWordUnitary e he).symm f w • familyCyclicWord e w) f := by
  change HasSum (fun w => (familyCyclicBasis e he).repr f w • familyCyclicWord e w) f
  simpa only [familyCyclicBasis_apply] using (familyCyclicBasis e he).hasSum_repr f

end FreeProbability.Fock

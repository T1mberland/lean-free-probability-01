import FreeProbability.Fock.SecondQuantizationPrefixIdentificationCompression
import FreeProbability.Fock.BoundaryCommutator

/-! # Genuine onto completed-word reversal and exact right operator transport -/
noncomputable section
open scoped Classical
namespace FreeProbability.Fock
variable {I : Type*}

/-- Actual onto unitary word reversal, on arbitrary completed word spaces including empty alphabets. -/
def wordReversalUnitary : WordSpace I ≃ₗᵢ[ℂ] WordSpace I :=
  LinearIsometryEquiv.ofSurjective reversalIsometry (fun f => ⟨reversal f, reversal_reversal f⟩)

@[simp] theorem wordReversalUnitary_apply (f : WordSpace I) : wordReversalUnitary f = reversal f := rfl

@[simp] theorem wordReversalUnitary_symm_apply (f : WordSpace I) :
    wordReversalUnitary.symm f = reversal f := by
  apply wordReversalUnitary.injective
  rw [LinearIsometryEquiv.apply_symm_apply, wordReversalUnitary_apply, reversal_reversal]

@[simp] theorem wordReversalUnitary_word (w : List I) :
    wordReversalUnitary (word w) = word w.reverse := reversal_word w

@[simp] theorem wordReversalUnitary_vacuum :
    wordReversalUnitary (vacuum : WordSpace I) = vacuum := reversal_vacuum

/-- Exact conjugation gives the existing literal right creator. -/
theorem wordReversalUnitary_conj_creation (i : I) :
    wordReversalUnitary.conjStarAlgEquiv (creation i) = rightCreation i := by
  apply ContinuousLinearMap.ext
  intro f
  change wordReversalUnitary (creation i (wordReversalUnitary.symm f)) = rightCreation i f
  rw [wordReversalUnitary_symm_apply, wordReversalUnitary_apply]
  rfl

/-- Actual Hilbert adjoint gives the existing right annihilator. -/
theorem wordReversalUnitary_conj_annihilation (i : I) :
    wordReversalUnitary.conjStarAlgEquiv (annihilation i) = rightAnnihilation i := by
  change wordReversalUnitary.conjStarAlgEquiv (star (creation i)) = star (rightCreation i)
  rw [map_star, wordReversalUnitary_conj_creation]

theorem wordReversalUnitary_conj_semicircular (i : I) :
    wordReversalUnitary.conjStarAlgEquiv (semicircular i) = rightSemicircular i := by
  apply ContinuousLinearMap.ext
  intro f
  change wordReversalUnitary (semicircular i (wordReversalUnitary.symm f)) = rightSemicircular i f
  rw [wordReversalUnitary_symm_apply, wordReversalUnitary_apply]
  rfl

end FreeProbability.Fock

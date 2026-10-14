import FreeProbability.Fock.SecondQuantizationSuffixOutside

/-! # Literal suffix bounded-operator representation and outside left commutation -/
noncomputable section
open scoped Classical
namespace FreeProbability.Fock
variable {I J : Type*}

theorem wordReversalUnitary_conj_involutive (T : WordSpace I →L[ℂ] WordSpace I) :
    wordReversalUnitary.conjStarAlgEquiv (wordReversalUnitary.conjStarAlgEquiv T) = T := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    wordReversalUnitary_apply, wordReversalUnitary_symm_apply, reversal_reversal]

theorem wordReversalUnitary_conj_rightCreation (i : I) :
    wordReversalUnitary.conjStarAlgEquiv (rightCreation i) = creation i := by
  rw [← wordReversalUnitary_conj_creation, wordReversalUnitary_conj_involutive]

/-- Actual suffix representation of ALL source word-space bounded operators. -/
def wordSuffixEmbedding : (WordSpace I →L[ℂ] WordSpace I) →⋆ₐ[ℂ]
    (WordSpace (Sum I J) →L[ℂ] WordSpace (Sum I J)) :=
  wordReversalUnitary.conjStarAlgEquiv.toStarAlgHom.comp
    (prefixOperatorEmbedding.comp wordReversalUnitary.conjStarAlgEquiv.toStarAlgHom)

/-- No source commutant assumption: ALL suffix operators commute with outside LEFT creation. -/
theorem wordSuffixEmbedding_commute_creation_outside (T : WordSpace I →L[ℂ] WordSpace I) (j : J) :
    Commute (wordSuffixEmbedding T) (creation (Sum.inr j)) := by
  have h := congrArg wordReversalUnitary.conjStarAlgEquiv
    (prefixOperatorEmbedding_commute_rightCreation_outside
      (wordReversalUnitary.conjStarAlgEquiv T) j).eq
  rw [map_mul, map_mul, wordReversalUnitary_conj_rightCreation] at h
  exact h

/-- Adjoint transport gives outside left annihilator commutation for ALL source operators. -/
theorem wordSuffixEmbedding_commute_annihilation_outside (T : WordSpace I →L[ℂ] WordSpace I) (j : J) :
    Commute (wordSuffixEmbedding T) (annihilation (Sum.inr j)) := by
  have h := congrArg star (wordSuffixEmbedding_commute_creation_outside (star T) j).eq
  simp only [star_mul, map_star, star_star] at h
  exact h.symm

end FreeProbability.Fock

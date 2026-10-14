import FreeProbability.Fock.WickSuffixGramFinite
import FreeProbability.Fock.FamilyCyclicBasisNativeEquiv

/-! # Actual prescribed-family OU transport to closed word operators -/
noncomputable section
open scoped Classical
namespace FreeProbability.Fock
variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Actual Wick operator in the canonical word norm closure. -/
def suffixGramClosedWick (w : List I) : closedSemicircularAlgebra I :=
  ⟨wick w, (semicircularAlgebra I).le_topologicalClosure (wick_mem_algebra w)⟩

/-- The native inverse transport sends closed word Wick operators to the original ones. -/
theorem familyNativeWordEquiv_symm_closedWick (e : I → H) (he : Orthonormal ℂ e)
    (w : List I) :
    (familyNativeWordEquiv e he).symm (suffixGramClosedWick w) = familyClosedWick e w := by
  apply (familyNativeWordEquiv e he).injective
  change familyNativeWordEquiv e he
    ((familyNativeWordEquiv e he).symm (suffixGramClosedWick w)) =
      familyNativeWordEquiv e he (familyClosedWick e w)
  rw [StarAlgEquiv.apply_symm_apply]
  apply Subtype.ext
  exact (familyNativeWordRepresentation_Wick e he w).symm

/-- The genuine whole-double-commutant OU map has the represented Wick eigenvalue. -/
theorem familyWordRepresentation_OU_Wick (e : I → H) (he : Orthonormal ℂ e)
    (t : ℝ) (ht : 0 ≤ t) (w : List I) :
    familyWordRepresentation e he
      (ouVonNeumannTimeCP e t ht (ouCyclicNativeInclusion e (familyClosedWick e w))) =
        degreeWeight t w.length • wick w := by
  apply sub_eq_zero.mp
  apply eq_zero_of_commute_right_of_vacuum_eq_zero
  · intro i
    exact Commute.sub_left (familyWordRepresentation_commute_right e he _ i)
      (commute_right_of_mem_semicircularAlgebra
        ((semicircularAlgebra I).smul_mem (wick_mem_algebra w) _) i)
  · rw [sub_apply, familyWordRepresentation_vacuum, smul_apply, wick_vacuum]
    apply sub_eq_zero.mpr
    apply lp.ext
    funext v
    rw [familyVonNeumannWordCoefficients_OU, familyVonNeumannWordCoefficients_Wick]
    by_cases hv : v = w
    · subst v
      rfl
    · simp [word, lp.single_apply, hv]

/-- Actual word-side linear map, transported from the proved whole-family CP map.
Its codomain is the full bounded-operator algebra; no range preservation is presumed. -/
def actualFamilyWordOU (e : I → H) (he : Orthonormal ℂ e) (t : ℝ) (ht : 0 ≤ t) :
    closedSemicircularAlgebra I →ₗ[ℂ] (WordSpace I →L[ℂ] WordSpace I) :=
  (familyWordRepresentation e he).toLinearMap.comp
    ((ouVonNeumannTimeCP e t ht).toLinearMap.comp
      ((ouCyclicNativeInclusion e).toLinearMap.comp
        (familyNativeWordEquiv e he).symm.toStarAlgHom.toLinearMap))

@[simp] theorem actualFamilyWordOU_closedWick (e : I → H) (he : Orthonormal ℂ e)
    (t : ℝ) (ht : 0 ≤ t) (w : List I) :
    actualFamilyWordOU e he t ht (suffixGramClosedWick w) =
      degreeWeight t w.length • wick w := by
  change familyWordRepresentation e he
    (ouVonNeumannTimeCP e t ht (ouCyclicNativeInclusion e
      ((familyNativeWordEquiv e he).symm (suffixGramClosedWick w)))) = _
  rw [familyNativeWordEquiv_symm_closedWick]
  exact familyWordRepresentation_OU_Wick e he t ht w

end FreeProbability.Fock

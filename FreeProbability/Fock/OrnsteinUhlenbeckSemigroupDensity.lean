import FreeProbability.Fock.OrnsteinUhlenbeckSemigroupWickAction

/-! # Genuine norm-density extension of continuous linear Wick identities -/
noncomputable section
open scoped Classical
namespace FreeProbability.Fock
variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Continuous linear maps on the entire native C-star closure are determined by actual Wick words. -/
theorem familyContinuousLinearMap_ext_Wick (e : I → H)
    (F G : tensorFamilyAlgebra e →L[ℂ] tensorFamilyAlgebra e)
    (hW : ∀ w : List I, F (familyClosedWick e w) = G (familyClosedWick e w)) : F = G := by
  let S := (F - G).toLinearMap.ker.map (tensorFamilyAlgebra e).val.toLinearMap
  have hs : familyWickSpan e ≤ S := by
    apply Submodule.span_le.mpr
    intro T hT
    obtain ⟨w, rfl⟩ := hT
    apply Submodule.mem_map.mpr
    refine ⟨familyClosedWick e w, ?_, rfl⟩
    change F (familyClosedWick e w) - G (familyClosedWick e w) = 0
    exact sub_eq_zero.mpr (hW w)
  let P := StarAlgebra.adjoin ℂ (Set.range (tensorFamilyField e))
  let j : P → tensorFamilyAlgebra e := StarSubalgebra.inclusion P.le_topologicalClosure
  have hd : DenseRange j := by
    change DenseRange (Set.inclusion P.le_topologicalClosure)
    apply (denseRange_inclusion_iff P.le_topologicalClosure).mpr
    exact Set.Subset.rfl
  have hp : ∀ T : P, F (j T) = G (j T) := by
    intro T
    have hm : (T : TensorFullFock H →L[ℂ] TensorFullFock H) ∈ S :=
      hs (family_polynomial_mem_WickSpan e T.property)
    obtain ⟨U, hU, hval⟩ := Submodule.mem_map.mp hm
    have heq : U = j T := Subtype.ext hval
    change F U - G U = 0 at hU
    rw [heq] at hU
    exact sub_eq_zero.mp hU
  apply DFunLike.ext'
  apply Continuous.ext_on hd F.continuous G.continuous
  rintro _ ⟨T, rfl⟩
  exact hp T

/-- Actual OU contraction as a continuous linear endomorphism of the native C-star algebra. -/
def familyOUContinuous (e : I → H) (he : Orthonormal ℂ e)
    (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1) : tensorFamilyAlgebra e →L[ℂ] tensorFamilyAlgebra e :=
  (familyOU e he r s hrs).toLinearMap.mkContinuous 1 (by
    intro T
    change ‖familyOU e he r s hrs T‖ ≤ 1 * ‖T‖
    rw [one_mul]
    exact norm_familyOU_le e he r s hrs T)

/-- Actual time-parametrized OU contraction on the entire native norm closure. -/
def familyOUTimeContinuous (e : I → H) (he : Orthonormal ℂ e) (t : ℝ) (ht : 0 ≤ t) :
    tensorFamilyAlgebra e →L[ℂ] tensorFamilyAlgebra e :=
  familyOUContinuous e he (ouCosine t) (ouSine t) (ouRotation_parameters t ht)

end FreeProbability.Fock

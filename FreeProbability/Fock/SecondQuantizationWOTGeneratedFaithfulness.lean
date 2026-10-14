import FreeProbability.Fock.SecondQuantizationWOTGeneratedCompression

/-! # Separating vacuum on actual WOT-generated orthonormal field algebras

The right fields of the full adapted basis, rather than just the prescribed
possibly nonspanning family, supply the separating-vacuum argument.
-/
noncomputable section
open scoped Classical
namespace FreeProbability.Fock

/-- Actual unitary conjugation as a star algebra equivalence on WOT operator types. -/
def wotUnitaryConjugationEquiv {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (U : E ≃ₗᵢ[ℂ] F) : (E →WOT[ℂ] E) ≃⋆ₐ[ℂ] (F →WOT[ℂ] F) where
  toFun T := ContinuousLinearMapWOT.ofCLM (U.conjStarAlgEquiv T.toCLM)
  invFun T := ContinuousLinearMapWOT.ofCLM (U.conjStarAlgEquiv.symm T.toCLM)
  left_inv T := congrArg ContinuousLinearMapWOT.ofCLM (U.conjStarAlgEquiv.symm_apply_apply T.toCLM)
  right_inv T := congrArg ContinuousLinearMapWOT.ofCLM (U.conjStarAlgEquiv.apply_symm_apply T.toCLM)
  map_mul' T S := congrArg ContinuousLinearMapWOT.ofCLM (map_mul U.conjStarAlgEquiv T.toCLM S.toCLM)
  map_add' T S := congrArg ContinuousLinearMapWOT.ofCLM (map_add U.conjStarAlgEquiv T.toCLM S.toCLM)
  map_smul' c T := congrArg ContinuousLinearMapWOT.ofCLM (map_smul U.conjStarAlgEquiv.toAlgEquiv c T.toCLM)
  map_star' T := congrArg ContinuousLinearMapWOT.ofCLM (map_star U.conjStarAlgEquiv T.toCLM)

def wordSemicircularWOTAlgebra (J : Type*) : StarSubalgebra ℂ (WordSpace J →WOT[ℂ] WordSpace J) :=
  (StarAlgebra.adjoin ℂ (Set.range (fun j : J =>
    ContinuousLinearMapWOT.ofCLM (semicircular j)))).topologicalClosure

theorem wordSemicircularWOTAlgebra_commute_right {J : Type*}
    {T : WordSpace J →WOT[ℂ] WordSpace J} (hT : T ∈ wordSemicircularWOTAlgebra J) (j : J) :
    Commute T.toCLM (rightSemicircular j) := by
  let R := ContinuousLinearMapWOT.ofCLM (rightSemicircular j)
  let B := StarSubalgebra.centralizer ℂ ({R} : Set _)
  have hp : StarAlgebra.adjoin ℂ (Set.range (fun i : J =>
      ContinuousLinearMapWOT.ofCLM (semicircular i))) ≤ B := by
    apply StarAlgebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
    intro Q hQ
    have he : Q = R := Set.mem_singleton_iff.mp hQ
    subst Q
    have hs : star R = R := congrArg ContinuousLinearMapWOT.ofCLM
      (adjoint_rightSemicircular j)
    rw [hs]
    exact ⟨congrArg ContinuousLinearMapWOT.ofCLM
      (commute_semicircular_rightSemicircular i j).eq.symm,
      congrArg ContinuousLinearMapWOT.ofCLM
      (commute_semicircular_rightSemicircular i j).eq.symm⟩
  have hc : IsClosed (B : Set (WordSpace J →WOT[ℂ] WordSpace J)) := by
    change IsClosed (({R} ∪ star {R} : Set _).centralizer)
    exact Set.isClosed_centralizer _
  have hb := StarSubalgebra.topologicalClosure_minimal hp hc hT
  exact (congrArg ContinuousLinearMapWOT.toCLM
    ((((StarSubalgebra.mem_centralizer_iff ℂ).mp hb) R (Set.mem_singleton R)).1)).symm

/-- Full right-field totality makes the actual WOT vacuum separating. -/
theorem wordSemicircularWOTAlgebra_vacuum_separating {J : Type*}
    {T : WordSpace J →WOT[ℂ] WordSpace J} (hT : T ∈ wordSemicircularWOTAlgebra J)
    (hzero : T (vacuum : WordSpace J) = 0) : T = 0 := by
  apply ContinuousLinearMapWOT.toCLM_injective
  exact eq_zero_of_commute_right_of_vacuum_eq_zero T.toCLM
    (wordSemicircularWOTAlgebra_commute_right hT) hzero

variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace OrthonormalFamilyExtension
variable {e : I → H} (d : OrthonormalFamilyExtension e)

/-- Reverse actual tensor unitary sends the whole native WOT closure into the full adapted closure. -/
theorem tensorFamilyWOTAlgebra_maps_into {T : TensorFullFock H →WOT[ℂ] TensorFullFock H}
    (hT : T ∈ tensorFamilyWOTAlgebra e) :
    wotUnitaryConjugationEquiv d.tensorTransport.symm T ∈ wordSemicircularWOTAlgebra d.indices := by
  let F := wotUnitaryConjugationEquiv d.tensorTransport.symm
  let B := (wordSemicircularWOTAlgebra d.indices).comap F.toStarAlgHom
  have hp : StarAlgebra.adjoin ℂ (Set.range (fun i =>
      ContinuousLinearMapWOT.ofCLM (tensorFamilyField e i))) ≤ B := by
    apply StarAlgebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    change ContinuousLinearMapWOT.ofCLM
      (d.tensorOperatorTransport.symm (tensorFamilyField e i)) ∈ wordSemicircularWOTAlgebra d.indices
    have he : d.tensorOperatorTransport.symm (tensorFamilyField e i) = d.field i := by
      apply d.tensorOperatorTransport.injective
      change d.tensorOperatorTransport (d.tensorOperatorTransport.symm (tensorFamilyField e i)) =
        d.tensorOperatorTransport (d.field i)
      rw [StarAlgEquiv.apply_symm_apply, d.tensorOperatorTransport_field]
      rfl
    rw [he, d.field_eq_semicircular]
    exact (StarAlgebra.adjoin ℂ (Set.range (fun j : d.indices =>
      ContinuousLinearMapWOT.ofCLM (semicircular j)))).le_topologicalClosure
      (StarAlgebra.subset_adjoin ℂ _ (Set.mem_range_self (d.index i)))
  have hc : IsClosed (B : Set (TensorFullFock H →WOT[ℂ] TensorFullFock H)) :=
    (StarAlgebra.adjoin ℂ (Set.range (fun j : d.indices =>
      ContinuousLinearMapWOT.ofCLM (semicircular j)))).isClosed_topologicalClosure.preimage
      (unitaryConjugationWOT_continuous d.tensorTransport.symm)
  exact StarSubalgebra.topologicalClosure_minimal hp hc hT

include d in
/-- The vacuum is separating in the fixed native tensor model, using the full adapted right basis. -/
theorem tensorFamilyWOTAlgebra_vacuum_separating {T : TensorFullFock H →WOT[ℂ] TensorFullFock H}
    (hT : T ∈ tensorFamilyWOTAlgebra e) (hzero : T (tensorVacuum H) = 0) : T = 0 := by
  let S := wotUnitaryConjugationEquiv d.tensorTransport.symm T
  have hs : S = 0 := by
    apply wordSemicircularWOTAlgebra_vacuum_separating (d.tensorFamilyWOTAlgebra_maps_into hT)
    change d.tensorTransport.symm (T (d.tensorTransport d.vacuum)) = 0
    rw [d.tensorTransport_vacuum, hzero, map_zero]
  exact (wotUnitaryConjugationEquiv d.tensorTransport.symm).injective
    (hs.trans (map_zero _).symm)
end OrthonormalFamilyExtension

/-- No spanning or countability assumption is needed for the native WOT separating vacuum. -/
theorem tensorFamilyWOTAlgebra_vacuum_separating (e : I → H) (he : Orthonormal ℂ e)
    {T : TensorFullFock H →WOT[ℂ] TensorFullFock H}
    (hT : T ∈ tensorFamilyWOTAlgebra e) (hzero : T (tensorVacuum H) = 0) : T = 0 :=
  (orthonormalFamilyExtension he).tensorFamilyWOTAlgebra_vacuum_separating hT hzero

/-- Faithfulness of the actual vacuum quadratic form on the full native WOT closure. -/
theorem tensorFamilyWOTAlgebra_vacuum_faithful (e : I → H) (he : Orthonormal ℂ e)
    {T : TensorFullFock H →WOT[ℂ] TensorFullFock H}
    (hT : T ∈ tensorFamilyWOTAlgebra e)
    (hzero : (tensorVacuumState H).expectation (star T.toCLM * T.toCLM) = 0) : T = 0 := by
  apply tensorFamilyWOTAlgebra_vacuum_separating e he hT
  rw [tensorVacuumState_expectation, mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K,
    sq_eq_zero_iff] at hzero
  have hn : ‖T.toCLM (tensorVacuum H)‖ = 0 := by
    simpa using congrArg Complex.re hzero
  exact norm_eq_zero.mp hn

end FreeProbability.Fock

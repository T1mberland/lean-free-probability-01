import FreeProbability.Fock.OrnsteinUhlenbeckL2WickVacuum

/-! # Actual vacuum implementation of native OU and true vacuum L² contraction -/
noncomputable section
open scoped Classical InnerProductSpace
namespace FreeProbability.Fock
variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Genuine bounded vacuum evaluation on the actual native C-star algebra. -/
def familyVacuumVector (e : I → H) : tensorFamilyAlgebra e →L[ℂ] TensorFullFock H :=
  ({ toFun := fun T => (T : TensorFullFock H →L[ℂ] TensorFullFock H) (tensorVacuum H)
     map_add' := by intro T S; rfl
     map_smul' := by intro c T; rfl } : tensorFamilyAlgebra e →ₗ[ℂ] TensorFullFock H).mkContinuous 1 (by
    intro T
    have ht := (T : TensorFullFock H →L[ℂ] TensorFullFock H).le_opNorm (tensorVacuum H)
    rw [norm_tensorVacuum, mul_one] at ht
    exact ht.trans (one_mul _).symm.le)

/-- Genuine Wick norm-density extensionality, with any normed complex target. -/
theorem familyContinuousLinearMap_ext_Wick_target {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (e : I → H) (F G : tensorFamilyAlgebra e →L[ℂ] E)
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

/-- Actual OU vacuum implementation on all native C-star elements, proved by genuine Wick density. -/
theorem familyOUTime_vacuum_intertwining (e : I → H) (he : Orthonormal ℂ e) (t : ℝ) (ht : 0 ≤ t) :
    (familyVacuumVector e).comp (familyOUTimeContinuous e he t ht) =
      (degreeDamping H t ht).comp (familyVacuumVector e) := by
  apply familyContinuousLinearMap_ext_Wick_target e
  intro w
  have hOU := congrArg (familyVacuumVector e) (familyOUTime_Wick e he t ht w)
  have hD := degreeDamping_familyClosedWick_vacuum e t ht w
  change familyVacuumVector e (familyOUTime e he t ht (familyClosedWick e w)) =
    degreeDamping H t ht (familyVacuumVector e (familyClosedWick e w))
  rw [map_smul] at hOU
  exact hOU.trans hD.symm

/-- Pointwise actual equality OU(T)Ω = Dₜ(TΩ), for every element of the native closure. -/
theorem familyOUTime_vacuum_vector (e : I → H) (he : Orthonormal ℂ e) (t : ℝ) (ht : 0 ≤ t)
    (T : tensorFamilyAlgebra e) :
    familyVacuumVector e (familyOUTime e he t ht T) = degreeDamping H t ht (familyVacuumVector e T) :=
  DFunLike.congr_fun (familyOUTime_vacuum_intertwining e he t ht) T

/-- True vacuum L² contraction, rather than an operator-norm surrogate. -/
theorem familyOUTime_vacuum_norm_le (e : I → H) (he : Orthonormal ℂ e) (t : ℝ) (ht : 0 ≤ t)
    (T : tensorFamilyAlgebra e) :
    ‖familyVacuumVector e (familyOUTime e he t ht T)‖ ≤ ‖familyVacuumVector e T‖ := by
  rw [familyOUTime_vacuum_vector]
  exact norm_degreeDamping_le H t ht _

/-- The actual restricted state quadratic form is the actual squared vacuum norm. -/
theorem familyVacuumState_star_self_norm (e : I → H) (T : tensorFamilyAlgebra e) :
    (tensorFamilyVacuumState e).expectation (star T * T) = (‖familyVacuumVector e T‖ : ℂ) ^ 2 := by
  change (tensorVacuumState H).expectation (star (T : TensorFullFock H →L[ℂ] TensorFullFock H) * T) = _
  rw [tensorVacuumState_expectation, mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  rfl

/-- True state L² quadratic inequality, in real-valued form, on the entire native C-star algebra. -/
theorem familyOUTime_state_L2_le (e : I → H) (he : Orthonormal ℂ e) (t : ℝ) (ht : 0 ≤ t)
    (T : tensorFamilyAlgebra e) :
    ((tensorFamilyVacuumState e).expectation
      (star (familyOUTime e he t ht T) * familyOUTime e he t ht T)).re ≤
        ((tensorFamilyVacuumState e).expectation (star T * T)).re := by
  rw [familyVacuumState_star_self_norm, familyVacuumState_star_self_norm]
  simp only [← Complex.ofReal_pow, Complex.ofReal_re]
  exact pow_le_pow_left₀ (norm_nonneg _) (familyOUTime_vacuum_norm_le e he t ht T) 2

end FreeProbability.Fock

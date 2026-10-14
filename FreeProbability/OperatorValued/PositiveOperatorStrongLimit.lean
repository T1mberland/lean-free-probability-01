import FreeProbability.OperatorValued.PositiveOperatorMonotoneCauchy

/-! # Genuine strong operator limits and strong closedness of the positive cone -/
noncomputable section
open scoped InnerProductSpace Topology
open Filter
namespace FreeProbability
variable {J H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Canonical Loewner positivity passes to an actual pointwise strong operator limit. -/
theorem positiveOperator_nonneg_of_strong_tendsto {l : Filter J} [NeBot l]
    (T : J → (H →L[ℂ] H)) (S : H →L[ℂ] H) (hp : ∀ᶠ j in l, 0 ≤ T j)
    (hlim : ∀ x, Tendsto (fun j => T j x) l (𝓝 (S x))) : 0 ≤ S := by
  apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
  refine ⟨?_, ?_⟩
  · intro x y
    apply tendsto_nhds_unique_of_eventuallyEq ((hlim x).inner tendsto_const_nhds)
      (tendsto_const_nhds.inner (hlim y))
    filter_upwards [hp] with j hj
    exact (ContinuousLinearMap.nonneg_iff_isPositive.mp hj).inner_left_eq_inner_right x y
  · intro x
    have hi : Tendsto (fun j => inner ℂ (T j x) x) l (𝓝 (inner ℂ (S x) x)) :=
      (hlim x).inner (tendsto_const_nhds : Tendsto (fun _ : J => x) l (𝓝 x))
    have hr := RCLike.continuous_re.continuousAt.tendsto.comp hi
    exact ge_of_tendsto hr (hp.mono fun j hj =>
      (ContinuousLinearMap.nonneg_iff_isPositive.mp hj).re_inner_nonneg_left x)

/-- An arbitrary uniformly norm-bounded monotone directed net has a genuine bounded strong operator limit. -/
theorem monotoneOperator_exists_strong_limit [Preorder J] [NeBot (atTop : Filter J)]
    (T : J → (H →L[ℂ] H)) (hT : Monotone T) (M : ℝ) (hM : ∀ j, ‖T j‖ ≤ M) :
    ∃ S : H →L[ℂ] H, (∀ x, Tendsto (fun j => T j x) atTop (𝓝 (S x))) ∧ ‖S‖ ≤ M := by
  let f : H → H := fun x => (monotoneOperator_vector_tendsto T hT M hM x).choose
  have hf (x : H) : Tendsto (fun j => T j x) atTop (𝓝 (f x)) :=
    (monotoneOperator_vector_tendsto T hT M hM x).choose_spec
  have hb (x : H) : ‖f x‖ ≤ M * ‖x‖ :=
    le_of_tendsto (hf x).norm (Eventually.of_forall fun j =>
      ((T j).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hM j) (norm_nonneg x)))
  let L : H →ₗ[ℂ] H :=
    { toFun := f
      map_add' := by
        intro x y
        exact tendsto_nhds_unique (hf (x + y)) (by simpa only [map_add] using (hf x).add (hf y))
      map_smul' := by
        intro c x
        exact tendsto_nhds_unique (hf (c • x)) (by simpa only [map_smul, RingHom.id_apply] using (hf x).const_smul c) }
  let S : H →L[ℂ] H := L.mkContinuous M hb
  have hM0 : 0 ≤ M := by
    let : Nonempty J := nonempty_of_neBot (atTop : Filter J)
    exact (norm_nonneg (T (Classical.arbitrary J))).trans (hM _)
  exact ⟨S, hf, L.mkContinuous_norm_le hM0 hb⟩
end FreeProbability

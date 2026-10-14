import FreeProbability.OperatorValued.PositiveOperatorStrongLimit

/-! # Actual directed Loewner suprema and strong closedness of commutants -/
noncomputable section
open scoped Topology
open Filter
namespace FreeProbability
variable {J H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- The strong limit of an arbitrary monotone directed operator net is its actual Loewner least upper bound. -/
theorem monotoneOperator_strong_limit_isLUB [Preorder J] [NeBot (atTop : Filter J)]
    (T : J → (H →L[ℂ] H)) (hT : Monotone T) (S : H →L[ℂ] H)
    (hlim : ∀ x, Tendsto (fun j => T j x) atTop (𝓝 (S x))) : IsLUB (Set.range T) S := by
  constructor
  · rintro _ ⟨i, rfl⟩
    apply sub_nonneg.mp
    apply positiveOperator_nonneg_of_strong_tendsto (l := atTop) (fun j => T j - T i) (S - T i)
    · filter_upwards [eventually_ge_atTop i] with j hij
      exact sub_nonneg.mpr (hT hij)
    · intro x
      simpa only [sub_apply] using
        (hlim x).sub (tendsto_const_nhds : Tendsto (fun _ : J => T i x) atTop (𝓝 (T i x)))
  · intro B hB
    apply sub_nonneg.mp
    apply positiveOperator_nonneg_of_strong_tendsto (l := atTop) (fun j => B - T j) (B - S)
    · exact Eventually.of_forall fun j => sub_nonneg.mpr (hB ⟨j, rfl⟩)
    · intro x
      simpa only [sub_apply] using
        (tendsto_const_nhds : Tendsto (fun _ : J => B x) atTop (𝓝 (B x))).sub (hlim x)

/-- Genuine monotone convergence and actual order supremum for any norm-bounded directed operator net. -/
theorem monotoneOperator_exists_isLUB [Preorder J] [NeBot (atTop : Filter J)]
    (T : J → (H →L[ℂ] H)) (hT : Monotone T) (M : ℝ) (hM : ∀ j, ‖T j‖ ≤ M) :
    ∃ S : H →L[ℂ] H, IsLUB (Set.range T) S ∧
      (∀ x, Tendsto (fun j => T j x) atTop (𝓝 (S x))) ∧ ‖S‖ ≤ M := by
  obtain ⟨S, hlim, hn⟩ := monotoneOperator_exists_strong_limit T hT M hM
  exact ⟨S, monotoneOperator_strong_limit_isLUB T hT S hlim, hlim, hn⟩

omit [CompleteSpace H] in
/-- A fixed commutant is closed under genuine pointwise strong limits. -/
theorem operatorCentralizer_mem_of_strong_tendsto {l : Filter J} [NeBot l]
    (C : Set (H →L[ℂ] H)) (T : J → (H →L[ℂ] H)) (S : H →L[ℂ] H)
    (hmem : ∀ᶠ j in l, T j ∈ C.centralizer)
    (hlim : ∀ x, Tendsto (fun j => T j x) l (𝓝 (S x))) : S ∈ C.centralizer := by
  intro B hB
  ext x
  apply tendsto_nhds_unique_of_eventuallyEq
    ((B.continuous.tendsto (S x)).comp (hlim x)) (hlim (B x))
  filter_upwards [hmem] with j hj
  exact congrArg (fun A : H →L[ℂ] H => A x) (hj B hB)

/-- Actual norm-bounded monotone suprema stay in the same literal double commutant. -/
theorem operatorDoubleCentralizer_exists_isLUB [Preorder J] [NeBot (atTop : Filter J)]
    (C : Set (H →L[ℂ] H)) (T : J → (H →L[ℂ] H)) (hT : Monotone T)
    (hmem : ∀ j, T j ∈ C.centralizer.centralizer) (M : ℝ) (hM : ∀ j, ‖T j‖ ≤ M) :
    ∃ S : H →L[ℂ] H, S ∈ C.centralizer.centralizer ∧ IsLUB (Set.range T) S ∧
      (∀ x, Tendsto (fun j => T j x) atTop (𝓝 (S x))) ∧ ‖S‖ ≤ M := by
  obtain ⟨S, hsup, hlim, hn⟩ := monotoneOperator_exists_isLUB T hT M hM
  exact ⟨S, operatorCentralizer_mem_of_strong_tendsto (l := atTop) C.centralizer T S
    (Eventually.of_forall hmem) hlim, hsup, hlim, hn⟩
end FreeProbability

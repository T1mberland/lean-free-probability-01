import FreeProbability.Fock.WordSpace

/-! Finite-word orthogonal projections on the completed word Fock space.
The alphabet may be empty or uncountable. -/
noncomputable section
open scoped InnerProductSpace ENNReal Classical
namespace FreeProbability.Fock
variable {I : Type*}

/-- Keep precisely the coordinates indexed by a finite set of words. -/
def finiteWordProjection (S : Finset (List I)) : WordSpace I →L[ℂ] WordSpace I :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨fun w => if w ∈ S then f w else 0,
        (lp.memℓp f).mono' (by intro w; split_ifs <;> simp)⟩
      map_add' := by
        intro f g; apply lp.ext; funext w
        change (if w ∈ S then f w + g w else 0) =
          (if w ∈ S then f w else 0) + (if w ∈ S then g w else 0)
        split_ifs <;> simp
      map_smul' := by
        intro c f; apply lp.ext; funext w
        change (if w ∈ S then c • f w else 0) = c • (if w ∈ S then f w else 0)
        split_ifs <;> simp }
    1 (by intro f; simpa using
      (lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (x := (⟨fun w => if w ∈ S then f w else 0,
          (lp.memℓp f).mono' (by intro w; split_ifs <;> simp)⟩ : WordSpace I))
        (y := f) (by
          intro w
          change ‖if w ∈ S then f w else 0‖ ≤ ‖f w‖
          split_ifs <;> simp)))

@[simp] theorem finiteWordProjection_apply (S : Finset (List I))
    (f : WordSpace I) (w : List I) :
    finiteWordProjection S f w = if w ∈ S then f w else 0 := rfl

 theorem norm_finiteWordProjection_apply_le (S : Finset (List I)) (f : WordSpace I) :
    ‖finiteWordProjection S f‖ ≤ ‖f‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro w
  simp only [finiteWordProjection_apply]
  split_ifs <;> simp

 theorem norm_finiteWordProjection_le (S : Finset (List I)) :
    ‖finiteWordProjection S‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa using norm_finiteWordProjection_apply_le S f

@[simp] theorem finiteWordProjection_idempotent (S : Finset (List I)) :
    (finiteWordProjection S).comp (finiteWordProjection S) = finiteWordProjection S := by
  ext f w
  simp only [ContinuousLinearMap.comp_apply, finiteWordProjection_apply]
  split_ifs <;> rfl

@[simp] theorem finiteWordProjection_adjoint (S : Finset (List I)) :
    (finiteWordProjection S).adjoint = finiteWordProjection S := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro f g
  simp only [lp.inner_eq_tsum]
  congr 1
  funext w
  simp only [finiteWordProjection_apply]
  split_ifs <;> simp

 theorem finiteWordProjection_eq_sum (S : Finset (List I)) (f : WordSpace I) :
    finiteWordProjection S f = ∑ w ∈ S, lp.single 2 w (f w) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    apply lp.ext; funext w
    simp [finiteWordProjection_apply]
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha, ← ih]
    apply lp.ext; funext w
    change (if w ∈ insert a S then f w else 0) =
      (lp.single 2 a (f a) : WordSpace I) w + (if w ∈ S then f w else 0)
    by_cases hwa : w = a
    · subst w; simp [lp.single_apply, ha]
    · simp [lp.single_apply, hwa]

/-- The range is contained in the finite-dimensional span of the retained word vectors. -/
theorem finiteWordProjection_mem_span (S : Finset (List I)) (f : WordSpace I) :
    finiteWordProjection S f ∈ Submodule.span ℂ (word '' (S : Set (List I))) := by
  classical
  rw [finiteWordProjection_eq_sum]
  apply Submodule.sum_mem
  intro w hw
  have hs : (lp.single 2 w (f w) : WordSpace I) = f w • word w := by
    simpa [word] using (lp.single_smul (E := fun _ : List I => ℂ) 2 w (f w) (1 : ℂ))
  rw [hs]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨w, hw, rfl⟩)

 theorem finiteWordProjection_finite_span (S : Finset (List I)) :
    FiniteDimensional ℂ (Submodule.span ℂ (word '' (S : Set (List I)))) :=
  FiniteDimensional.span_of_finite ℂ (S.finite_toSet.image word)

end FreeProbability.Fock

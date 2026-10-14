import FreeProbability.Fock.OrnsteinUhlenbeckEmbeddingEquiv
import FreeProbability.Fock.OrnsteinUhlenbeckDilationWick

/-! # Actual Wick words span the polynomial family algebra and are dense in its norm closure -/
noncomputable section
open scoped Classical InnerProductSpace
namespace FreeProbability.Fock
variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Actual recursive Wick operator in the prescribed original-vector family. -/
def familyWick (e : I → H) (w : List I) : TensorFullFock H →L[ℂ] TensorFullFock H :=
  tensorVectorWick (w.map e)

/-- Algebraic finite linear span of actual Wick operators. -/
def familyWickSpan (e : I → H) : Submodule ℂ (TensorFullFock H →L[ℂ] TensorFullFock H) :=
  Submodule.span ℂ (Set.range (familyWick e))

theorem familyWick_mem_span (e : I → H) (w : List I) : familyWick e w ∈ familyWickSpan e :=
  Submodule.subset_span ⟨w, rfl⟩

@[simp] theorem familyWick_nil (e : I → H) : familyWick e [] = 1 := rfl
@[simp] theorem familyWick_singleton (e : I → H) (i : I) : familyWick e [i] = tensorFamilyField e i := by
  simp [familyWick, tensorVectorWick, tensorFamilyField]

theorem familyWick_cons_cons (e : I → H) (i j : I) (w : List I) :
    familyWick e (i :: j :: w) = tensorFamilyField e i * familyWick e (j :: w) -
      inner ℂ (e i) (e j) • familyWick e w := rfl

/-- Left multiplication by a field preserves the actual finite Wick span. -/
theorem field_mul_mem_familyWickSpan (e : I → H) (i : I)
    {T : TensorFullFock H →L[ℂ] TensorFullFock H} (hT : T ∈ familyWickSpan e) :
    tensorFamilyField e i * T ∈ familyWickSpan e := by
  induction hT using Submodule.span_induction with
  | mem T hT =>
    obtain ⟨w, rfl⟩ := hT
    cases w with
    | nil => simpa using familyWick_mem_span e [i]
    | cons j w =>
      have heq : tensorFamilyField e i * familyWick e (j :: w) =
          familyWick e (i :: j :: w) + inner ℂ (e i) (e j) • familyWick e w := by
        rw [familyWick_cons_cons]
        abel
      rw [heq]
      exact (familyWickSpan e).add_mem (familyWick_mem_span e _)
        ((familyWickSpan e).smul_mem _ (familyWick_mem_span e _))
  | zero => simp
  | add T S _ _ hT hS => simpa only [mul_add] using (familyWickSpan e).add_mem hT hS
  | smul c T _ hT =>
    have heq : tensorFamilyField e i * (c • T) = c • (tensorFamilyField e i * T) := by
      apply ContinuousLinearMap.ext
      intro f
      simp [mul_apply_eq_comp]
    rw [heq]
    exact (familyWickSpan e).smul_mem c hT

/-- Left multiplication by any recursive Wick word preserves the finite span. -/
theorem familyWick_mul_mem_span (e : I → H) (w : List I)
    {T : TensorFullFock H →L[ℂ] TensorFullFock H} (hT : T ∈ familyWickSpan e) :
    familyWick e w * T ∈ familyWickSpan e := by
  induction w using List.twoStepInduction with
  | nil => simpa using hT
  | singleton i => simpa using field_mul_mem_familyWickSpan e i hT
  | cons_cons i j w hw hjw =>
    rw [familyWick_cons_cons, sub_mul, mul_assoc]
    have hm : (inner ℂ (e i) (e j) • familyWick e w) * T =
        inner ℂ (e i) (e j) • (familyWick e w * T) := by
      apply ContinuousLinearMap.ext
      intro f
      simp [mul_apply_eq_comp]
    rw [hm]
    exact (familyWickSpan e).sub_mem (field_mul_mem_familyWickSpan e i (hjw j))
      ((familyWickSpan e).smul_mem _ hw)

/-- The actual finite Wick span is a genuine unital algebra. -/
def familyWickSpanAlgebra (e : I → H) : Subalgebra ℂ (TensorFullFock H →L[ℂ] TensorFullFock H) where
  carrier := familyWickSpan e
  zero_mem' := (familyWickSpan e).zero_mem
  add_mem' := (familyWickSpan e).add_mem
  one_mem' := familyWick_mem_span e []
  mul_mem' := by
    intro T S hT hS
    induction hT using Submodule.span_induction with
    | mem T hT =>
      obtain ⟨w, rfl⟩ := hT
      exact familyWick_mul_mem_span e w hS
    | zero => simp
    | add T U _ _ hT hU =>
      rw [add_mul]
      exact (familyWickSpan e).add_mem hT hU
    | smul c T _ hT =>
      have hm : (c • T) * S = c • (T * S) := by
        apply ContinuousLinearMap.ext
        intro f
        simp [mul_apply_eq_comp]
      rw [hm]
      exact (familyWickSpan e).smul_mem c hT
  algebraMap_mem' c := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact (familyWickSpan e).smul_mem c (familyWick_mem_span e [])

/-- Every actual polynomial in the self-adjoint fields belongs to the finite Wick span. -/
theorem family_polynomial_mem_WickSpan (e : I → H)
    {T : TensorFullFock H →L[ℂ] TensorFullFock H}
    (hT : T ∈ StarAlgebra.adjoin ℂ (Set.range (tensorFamilyField e))) :
    T ∈ familyWickSpan e := by
  have hp : (StarAlgebra.adjoin ℂ (Set.range (tensorFamilyField e))).toSubalgebra ≤ familyWickSpanAlgebra e := by
    rw [StarAlgebra.adjoin_toSubalgebra]
    apply Algebra.adjoin_le
    intro T hT
    rcases hT with hT | hT
    · obtain ⟨i, rfl⟩ := hT
      change tensorFamilyField e i ∈ familyWickSpan e
      rw [← familyWick_singleton e i]
      exact familyWick_mem_span e [i]
    · change star T ∈ Set.range (tensorFamilyField e) at hT
      obtain ⟨i, hi⟩ := hT
      have hh := congrArg star hi
      change (tensorFamilyField e i).adjoint = star (star T) at hh
      rw [ou_tensorFamilyField_adjoint, star_star] at hh
      rw [← hh]
      change tensorFamilyField e i ∈ familyWickSpan e
      rw [← familyWick_singleton e i]
      exact familyWick_mem_span e [i]
  exact hp hT

/-- Every recursive Wick word is an actual polynomial in the prescribed fields. -/
theorem familyWick_mem_polynomial (e : I → H) (w : List I) :
    familyWick e w ∈ StarAlgebra.adjoin ℂ (Set.range (tensorFamilyField e)) := by
  induction w using List.twoStepInduction with
  | nil => exact (StarAlgebra.adjoin ℂ _).one_mem
  | singleton i =>
    rw [familyWick_singleton]
    exact StarAlgebra.subset_adjoin ℂ _ ⟨i, rfl⟩
  | cons_cons i j w hw hjw =>
    rw [familyWick_cons_cons]
    exact (StarAlgebra.adjoin ℂ _).sub_mem
      ((StarAlgebra.adjoin ℂ _).mul_mem (StarAlgebra.subset_adjoin ℂ _ ⟨i, rfl⟩) (hjw j))
      ((StarAlgebra.adjoin ℂ _).smul_mem hw _)

/-- The entire literal closed family algebra is in the norm closure of the finite Wick span. -/
theorem tensorFamilyAlgebra_mem_closure_WickSpan (e : I → H)
    {T : TensorFullFock H →L[ℂ] TensorFullFock H} (hT : T ∈ tensorFamilyAlgebra e) :
    T ∈ closure (familyWickSpan e : Set (TensorFullFock H →L[ℂ] TensorFullFock H)) := by
  rw [tensorFamilyAlgebra, ← SetLike.mem_coe, StarSubalgebra.topologicalClosure_coe] at hT
  exact closure_mono (fun _ h => family_polynomial_mem_WickSpan e h) hT

end FreeProbability.Fock

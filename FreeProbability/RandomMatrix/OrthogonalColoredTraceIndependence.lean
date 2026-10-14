import FreeProbability.RandomMatrix.OrthogonalColoredTracePerturbation

/-! # Whole-data independence for a selected Haar color -/

noncomputable section
open scoped Classical
namespace FreeProbability.Orthogonal
open MeasureTheory ProbabilityTheory

/-- The WHOLE dependent tuple of all other coordinates is independent of a
selected coordinate in a genuinely jointly independent finite family. -/
theorem indepFun_except_coordinate {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    {β : I → Type*} [∀ i, MeasurableSpace (β i)] (μ : Measure Ω)
    (f : ∀ i, Ω → β i) (hf : iIndepFun f μ) (hm : ∀ i, Measurable (f i)) (c : I) :
    IndepFun (fun ω (j : {j : I // j ≠ c}) => f j.val ω) (f c) μ := by
  let S : Finset I := Finset.univ.erase c
  let T : Finset I := {c}
  have hd : Disjoint S T := by simp [S, T]
  have hi := hf.indepFun_finset S T hd hm
  let φ : (∀ j : S, β j.val) → (∀ j : {j : I // j ≠ c}, β j.val) :=
    fun v j => v ⟨j.val, by simp [S, j.property]⟩
  let ψ : (∀ j : T, β j.val) → β c := fun v => v ⟨c, by simp [T]⟩
  have hφ : Measurable φ := by
    apply measurable_pi_iff.mpr
    intro j
    exact measurable_pi_apply _
  have hψ : Measurable ψ := measurable_pi_apply _
  exact hi.comp hφ hψ

universe u v w

/-- The data variable and every Haar color are separate coordinates of ONE
jointly independent family. Universe lifts impose no restriction on data types. -/
def AugmentedHaarDataType (Θ : Type u) (I : Type v) (n : Type w) [Fintype n] [DecidableEq n] :
    Unit ⊕ I → Type (max u w)
  | Sum.inl _ => ULift.{w} Θ
  | Sum.inr _ => ULift.{u} (Group n)

instance augmentedHaarDataType_measurableSpace {Θ : Type u} {I : Type v} {n : Type w}
    [MeasurableSpace Θ] [Fintype n] [DecidableEq n] (j : Unit ⊕ I) :
    MeasurableSpace (AugmentedHaarDataType Θ I n j) := by
  cases j <;> dsimp [AugmentedHaarDataType] <;> infer_instance

/-- Actual augmented sampling map, retaining the entire original input data. -/
def augmentedHaarVariables {Ω : Type*} {Θ : Type u} {I : Type v} {n : Type w}
    [Fintype n] [DecidableEq n] (Y : Ω → Θ) (X : I → Ω → Group n) :
    ∀ j, Ω → AugmentedHaarDataType Θ I n j
  | Sum.inl _ => fun ω => ULift.up (Y ω)
  | Sum.inr c => fun ω => ULift.up (X c ω)

/-- The selected Haar color is independent of the WHOLE original data and
all other Haar matrices, without assuming merely pairwise independence. -/
theorem augmentedHaar_except_independent {Ω : Type*} {Θ : Type u} {I : Type v} {n : Type w}
    [MeasurableSpace Ω] [MeasurableSpace Θ] [Fintype I] [Fintype n] [DecidableEq n]
    (μ : Measure Ω) (Y : Ω → Θ) (X : I → Ω → Group n)
    (hY : Measurable Y) (hX : ∀ c, Measurable (X c))
    (hi : iIndepFun (augmentedHaarVariables Y X) μ) (c : I) :
    IndepFun (fun ω (j : {j : Unit ⊕ I // j ≠ Sum.inr c}) =>
      augmentedHaarVariables Y X j.val ω) (X c) μ := by
  have hm (j : Unit ⊕ I) : Measurable (augmentedHaarVariables Y X j) := by
    cases j with
    | inl _ => exact MeasurableEquiv.ulift.symm.measurable.comp hY
    | inr c => exact MeasurableEquiv.ulift.symm.measurable.comp (hX c)
  have he := indepFun_except_coordinate μ (augmentedHaarVariables Y X) hi hm (Sum.inr c)
  exact he.comp measurable_id MeasurableEquiv.ulift.measurable

/-- All input data and all nonselected Haar coordinates, as one actual tuple. -/
abbrev ExceptHaarData (Θ : Type u) (I : Type v) (n : Type w) [Fintype n] [DecidableEq n] (c : I) :=
  ∀ j : {j : Unit ⊕ I // j ≠ Sum.inr c}, AugmentedHaarDataType Θ I n j.val

/-- Recover the entire original input data from the genuine except-color tuple. -/
def exceptHaarInputData {Θ : Type u} {I : Type v} {n : Type w} [Fintype n] [DecidableEq n]
    (c : I) (z : ExceptHaarData Θ I n c) : Θ :=
  (z ⟨Sum.inl (), by simp⟩).down

/-- Recover any actual nonselected orthogonal matrix from the same tuple. -/
def exceptHaarMatrix {Θ : Type u} {I : Type v} {n : Type w} [Fintype n] [DecidableEq n]
    (c d : I) (hd : d ≠ c) (z : ExceptHaarData Θ I n c) : Group n :=
  (z ⟨Sum.inr d, by simpa using hd⟩).down

/-- The original-data accessor is genuinely measurable. -/
theorem measurable_exceptHaarInputData {Θ : Type u} {I : Type v} {n : Type w}
    [MeasurableSpace Θ] [Fintype n] [DecidableEq n] (c : I) :
    Measurable (exceptHaarInputData (Θ := Θ) (n := n) c) :=
  MeasurableEquiv.ulift.measurable.comp (measurable_pi_apply _)

/-- Every nonselected matrix accessor is genuinely measurable. -/
theorem measurable_exceptHaarMatrix {Θ : Type u} {I : Type v} {n : Type w}
    [MeasurableSpace Θ] [Fintype n] [DecidableEq n] (c d : I) (hd : d ≠ c) :
    Measurable (exceptHaarMatrix (Θ := Θ) (n := n) c d hd) :=
  MeasurableEquiv.ulift.measurable.comp (measurable_pi_apply _)

/-- The original-data coordinate is the actual input variable in a realization. -/
theorem exceptHaarInputData_apply {Ω : Type*} {Θ : Type u} {I : Type v} {n : Type w}
    [Fintype n] [DecidableEq n] (Y : Ω → Θ) (X : I → Ω → Group n) (c : I) (ω : Ω) :
    exceptHaarInputData c (fun j => augmentedHaarVariables Y X j.val ω) = Y ω := rfl

/-- A nonselected matrix coordinate is the actual sampled orthogonal matrix. -/
theorem exceptHaarMatrix_apply {Ω : Type*} {Θ : Type u} {I : Type v} {n : Type w}
    [Fintype n] [DecidableEq n] (Y : Ω → Θ) (X : I → Ω → Group n)
    (c d : I) (hd : d ≠ c) (ω : Ω) :
    exceptHaarMatrix c d hd (fun j => augmentedHaarVariables Y X j.val ω) = X d ω := rfl

end FreeProbability.Orthogonal

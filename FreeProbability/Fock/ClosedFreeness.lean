import FreeProbability.Fock.Freeness

/-! # Free independence of the norm-closed canonical generator algebras -/

noncomputable section
open scoped Classical InnerProductSpace

namespace FreeProbability.Fock

variable {I : Type*}

private theorem zero_smul_operator (T : WordSpace I →L[ℂ] WordSpace I) : (0 : ℂ) • T = 0 := by
  ext f
  simp

/-- Centered elements of the closed one-generator algebra are limits of positive Wick degrees. -/
theorem centered_mem_closed_positiveOneColorSpan (i : I)
    {T : WordSpace I →L[ℂ] WordSpace I}
    (hT : T ∈ (Algebra.adjoin ℂ ({semicircular i} : Set _)).topologicalClosure)
    (hzero : vacuumExpectation T = 0) : T ∈ (positiveOneColorSpan i).topologicalClosure := by
  have hc : Continuous (fun U : WordSpace I →L[ℂ] WordSpace I =>
      U - vacuumExpectation U • (1 : WordSpace I →L[ℂ] WordSpace I)) :=
    continuous_id.sub ((vacuumContinuous I).continuous.smul continuous_const)
  have hm := map_mem_closure hc hT (fun U hU =>
    center_mem_positiveOneColorSpan i (mem_oneColorSpan_of_mem_adjoin i hU))
  change T ∈ closure (positiveOneColorSpan i : Set _)
  simpa [hzero, zero_smul_operator] using hm

/-- Vacuum orthogonality persists on the closed color sector. -/
theorem inner_vacuum_eq_zero_of_mem_closed_colorSector (i : I) {f : WordSpace I}
    (hf : f ∈ (colorSector i).topologicalClosure) :
    inner ℂ (vacuum : WordSpace I) f = 0 := by
  exact closure_minimal (fun g hg => inner_vacuum_eq_zero_of_mem_colorSector i hg)
    (isClosed_eq (innerSL ℂ (vacuum : WordSpace I)).continuous continuous_const) hf

/-- A closed centered generator operator sends the vacuum into its closed color sector. -/
theorem closed_positive_apply_vacuum (i : I)
    {T : WordSpace I →L[ℂ] WordSpace I} (hT : T ∈ (positiveOneColorSpan i).topologicalClosure) :
    T (vacuum : WordSpace I) ∈ (colorSector i).topologicalClosure := by
  have hsub : (positiveOneColorSpan i : Set (WordSpace I →L[ℂ] WordSpace I)) ⊆
      {U : WordSpace I →L[ℂ] WordSpace I | U vacuum ∈ (colorSector i).topologicalClosure} :=
    fun U hU => (colorSector i).le_topologicalClosure
      (positive_apply_word_mem_colorSector i hU [] (by simp))
  exact closure_minimal hsub
    ((colorSector i).isClosed_topologicalClosure.preimage
      (ContinuousLinearMap.apply ℂ (WordSpace I) vacuum).continuous) hT

/-- Both the operator and the input sector may be limits; continuity in each variable suffices. -/
theorem closed_positive_apply_colorSector (i j : I) (hij : i ≠ j)
    {T : WordSpace I →L[ℂ] WordSpace I} (hT : T ∈ (positiveOneColorSpan i).topologicalClosure)
    {f : WordSpace I} (hf : f ∈ (colorSector j).topologicalClosure) :
    T f ∈ (colorSector i).topologicalClosure := by
  have hpoly : ∀ g ∈ colorSector j, T g ∈ (colorSector i).topologicalClosure := by
    intro g hg
    have hsub : (positiveOneColorSpan i : Set (WordSpace I →L[ℂ] WordSpace I)) ⊆
        {U : WordSpace I →L[ℂ] WordSpace I | U g ∈ (colorSector i).topologicalClosure} :=
      fun U hU => (colorSector i).le_topologicalClosure
        (positive_apply_colorSector i j hij hU hg)
    exact closure_minimal hsub
      ((colorSector i).isClosed_topologicalClosure.preimage
        (ContinuousLinearMap.apply ℂ (WordSpace I) g).continuous) hT
  exact closure_minimal hpoly ((colorSector i).isClosed_topologicalClosure.preimage T.continuous) hf

/-- Arbitrary alternating centered closed-algebra products remain in a nonvacuum sector. -/
theorem alternating_closed_positive_product_mem_colorSector
    (a : I × (WordSpace I →L[ℂ] WordSpace I))
    (w : List (I × (WordSpace I →L[ℂ] WordSpace I)))
    (halt : (a :: w).IsChain (fun x y => x.1 ≠ y.1))
    (hmem : ∀ x ∈ a :: w, x.2 ∈ (positiveOneColorSpan x.1).topologicalClosure) :
    ((a :: w).map Prod.snd).prod (vacuum : WordSpace I) ∈ (colorSector a.1).topologicalClosure := by
  induction w generalizing a with
  | nil =>
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    exact closed_positive_apply_vacuum a.1 (hmem a (by simp))
  | cons b w ih =>
    have hchain := List.isChain_cons_cons.mp halt
    have hf := ih b hchain.2 (fun x hx => hmem x (by simp [hx]))
    simp only [List.map_cons, List.prod_cons, mul_apply_eq_comp]
    exact closed_positive_apply_colorSector a.1 b.1 hchain.1 (hmem a (by simp)) hf

/-- Free independence of all the actual norm-closed canonical generator algebras. -/
theorem freelyIndependent_semicircular_closed (I : Type*) :
    FreelyIndependent (vacuumState I).toProbabilitySpace
      (fun i => (Algebra.adjoin ℂ ({semicircular i} : Set (WordSpace I →L[ℂ] WordSpace I))).topologicalClosure) := by
  intro w hw halt hmem hzero
  cases w with
  | nil => exact (hw rfl).elim
  | cons a w =>
    apply inner_vacuum_eq_zero_of_mem_closed_colorSector a.1
    apply alternating_closed_positive_product_mem_colorSector a w halt
    intro x hx
    exact centered_mem_closed_positiveOneColorSpan x.1 (hmem x hx) (hzero x hx)

end FreeProbability.Fock

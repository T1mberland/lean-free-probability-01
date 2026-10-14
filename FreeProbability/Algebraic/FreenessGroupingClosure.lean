import FreeProbability.Algebraic.FreenessGroupingSpan
import FreeProbability.Algebraic.FreenessClosure

/-! # Grouped algebra membership, joins, and closed freeness -/

noncomputable section
namespace FreeProbability
variable {𝕜 A I J K : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]

/-- Every original algebra belongs to the algebra of its assigned group. -/
theorem le_groupedSubalgebra (B : I → Subalgebra 𝕜 A) (g : I → J) (i : I) :
    B i ≤ groupedSubalgebra B g (g i) := by
  intro a ha
  exact Algebra.subset_adjoin ⟨i, rfl, ha⟩

/-- The generated grouped algebra is exactly the join of the original
subalgebras in the grouping fiber, even for empty or infinite fibers. -/
theorem groupedSubalgebra_eq_iSup (B : I → Subalgebra 𝕜 A) (g : I → J) (j : J) :
    groupedSubalgebra B g j = ⨆ i : {i : I // g i = j}, B i.val := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro a ⟨i, hi, ha⟩
    exact (le_iSup (fun i : {i : I // g i = j} => B i.val) ⟨i, hi⟩) ha
  · apply iSup_le
    intro i a ha
    exact Algebra.subset_adjoin ⟨i.val, i.property, ha⟩

/-- Repeated grouping is exactly grouping by the composite label function. -/
theorem groupedSubalgebra_comp (B : I → Subalgebra 𝕜 A) (g : I → J) (h : J → K) (k : K) :
    groupedSubalgebra (groupedSubalgebra B g) h k = groupedSubalgebra B (h ∘ g) k := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro a ⟨j, hj, ha⟩
    have hle : groupedSubalgebra B g j ≤ groupedSubalgebra B (h ∘ g) k := by
      apply Algebra.adjoin_le
      rintro b ⟨i, hi, hb⟩
      exact Algebra.subset_adjoin ⟨i, by change h (g i) = k; rw [hi, hj], hb⟩
    exact hle ha
  · apply Algebra.adjoin_le
    rintro a ⟨i, hi, ha⟩
    exact Algebra.subset_adjoin ⟨g i, hi, (le_groupedSubalgebra B g i) ha⟩

/-- Taking smaller original algebras makes every grouped algebra smaller. -/
theorem groupedSubalgebra_mono {B C : I → Subalgebra 𝕜 A} (g : I → J)
    (hBC : ∀ i, B i ≤ C i) (j : J) : groupedSubalgebra B g j ≤ groupedSubalgebra C g j := by
  apply Algebra.adjoin_le
  rintro a ⟨i, hi, ha⟩
  exact Algebra.subset_adjoin ⟨i, hi, hBC i ha⟩

variable [TopologicalSpace 𝕜] [T2Space 𝕜] [TopologicalSpace A]
    [IsTopologicalRing A] [ContinuousSMul 𝕜 A]

omit [TopologicalSpace 𝕜] [T2Space 𝕜] [ContinuousSMul 𝕜 A] in
/-- Every original algebra belongs to its actual closed grouped algebra. -/
theorem le_groupedSubalgebra_topologicalClosure (B : I → Subalgebra 𝕜 A)
    (g : I → J) (i : I) :
    B i ≤ (groupedSubalgebra B g (g i)).topologicalClosure :=
  (le_groupedSubalgebra B g i).trans (groupedSubalgebra B g (g i)).le_topologicalClosure

/-- Actual closed grouped algebras are free for a continuous expectation;
no trace, positivity, completeness, or finite-index hypothesis is needed. -/
theorem FreelyIndependent.groupedSubalgebra_topologicalClosure
    {φ : ProbabilitySpace 𝕜 A} {B : I → Subalgebra 𝕜 A} (hf : FreelyIndependent φ B)
    (hφ : Continuous φ.expectation) (g : I → J) :
    FreelyIndependent φ (fun j => (FreeProbability.groupedSubalgebra B g j).topologicalClosure) :=
  (hf.groupedSubalgebra g).topologicalClosure hφ

end FreeProbability

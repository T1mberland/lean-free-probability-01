import FreeProbability.Fock.ClosedFreeness
import FreeProbability.Fock.CStarModel
import FreeProbability.Algebraic.DistributionComparison

/-! # Freely independent canonical generators in the faithful tracial C-star model -/

noncomputable section
open scoped Classical

namespace FreeProbability

namespace Fock

variable {I : Type*}

/-- The closed one-generator algebra as a subalgebra of the faithful tracial ambient algebra. -/
def closedGeneratorAlgebra (i : I) : Subalgebra ℂ (closedSemicircularAlgebra I) :=
  ((Algebra.adjoin ℂ ({semicircular i} : Set (WordSpace I →L[ℂ] WordSpace I))).topologicalClosure).comap
    (closedSemicircularAlgebra I).val

/-- The canonical closed generator lies in its own single-generator algebra. -/
theorem closedSemicircular_mem_closedGeneratorAlgebra (i : I) :
    closedSemicircular i ∈ closedGeneratorAlgebra i :=
  (Algebra.adjoin ℂ ({semicircular i} : Set (WordSpace I →L[ℂ] WordSpace I))).le_topologicalClosure
    (Algebra.self_mem_adjoin_singleton ℂ (semicircular i))

/-- Arbitrary-cardinality free family inside the genuine faithful tracial C-star probability space. -/
theorem freelyIndependent_closedGeneratedVacuumState (I : Type*) :
    FreelyIndependent (𝕜 := ℂ) (A := closedSemicircularAlgebra I) (I := I)
      (closedGeneratedVacuumState I).toProbabilitySpace
      (closedGeneratorAlgebra (I := I)) := by
  intro w hw halt hmem hzero
  let f := (closedSemicircularAlgebra I).val
  let g : I × closedSemicircularAlgebra I → I × (WordSpace I →L[ℂ] WordSpace I) :=
    fun x => (x.1, f x.2)
  have halt' : (w.map g).IsChain (fun x y => x.1 ≠ y.1) :=
    (List.isChain_map g).mpr halt
  have hm : ∀ x ∈ w.map g,
      x.2 ∈ (Algebra.adjoin ℂ ({semicircular x.1} : Set _)).topologicalClosure := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact hmem y hy
  have hz : ∀ x ∈ w.map g, (vacuumState I).expectation x.2 = 0 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact hzero y hy
  have hr := freelyIndependent_semicircular_closed I (w.map g) (by simpa using hw) halt' hm hz
  change vacuumExpectation (f (w.map Prod.snd).prod) = 0
  simpa [g, List.map_map, Function.comp_def, map_list_prod, f] using hr

end Fock
end FreeProbability

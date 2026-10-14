import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import Mathlib.Order.Preorder.Finite

/-! # Möbius invariance of finite-poset order isomorphisms -/

namespace FreeProbability

/-- Actual incidence-algebra Möbius values are invariant under order
isomorphisms of finite posets, even over a noncommutative coefficient ring. -/
theorem incidence_mu_orderIso {α β 𝕜 : Type*} [PartialOrder α] [PartialOrder β]
    [Finite α] [DecidableEq α] [DecidableEq β] [LocallyFiniteOrder α] [LocallyFiniteOrder β] [Ring 𝕜]
    (e : α ≃o β) (a b : α) :
    IncidenceAlgebra.mu 𝕜 (e a) (e b) = IncidenceAlgebra.mu 𝕜 a b := by
  classical
  revert a
  refine WellFoundedLT.induction (motive := fun b => ∀ a,
    IncidenceAlgebra.mu 𝕜 (e a) (e b) = IncidenceAlgebra.mu 𝕜 a b) b ?_
  intro b ih a
  rw [IncidenceAlgebra.mu_apply, IncidenceAlgebra.mu_apply]
  simp only [e.injective.eq_iff]
  split_ifs with hab
  · rfl
  congr 1
  symm
  apply Finset.sum_bij (fun c _ => e c)
  · intro c hc
    obtain ⟨hac, hcb⟩ := Finset.mem_Ico.mp hc
    exact Finset.mem_Ico.mpr ⟨e.monotone hac, e.strictMono hcb⟩
  · intro c _ d _ he
    exact e.injective he
  · intro d hd
    refine ⟨e.symm d, ?_, e.apply_symm_apply d⟩
    obtain ⟨had, hdb⟩ := Finset.mem_Ico.mp hd
    apply Finset.mem_Ico.mpr
    exact ⟨by simpa only [e.symm_apply_apply] using e.symm.monotone had,
      by simpa only [e.symm_apply_apply] using e.symm.strictMono hdb⟩
  · intro c hc
    exact (ih c (Finset.mem_Ico.mp hc).2 a).symm

end FreeProbability

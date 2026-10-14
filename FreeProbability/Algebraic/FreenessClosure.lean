import FreeProbability.Algebraic.Freeness
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange

/-! # Freeness passes to topological closures

Only continuity of the expectation is needed. Positivity, traces, completeness,
and a norm are not required.
-/

namespace FreeProbability
variable {𝕜 A I : Type*} [Field 𝕜] [TopologicalSpace 𝕜] [T2Space 𝕜]
    [Ring A] [TopologicalSpace A] [IsTopologicalRing A] [Algebra 𝕜 A]
    [ContinuousSMul 𝕜 A]
namespace FreelyIndependent
variable {φ : ProbabilitySpace 𝕜 A} {B : I → Subalgebra 𝕜 A}

/-- Centered alternating products of closure elements vanish by continuity. -/
theorem centered_ofFn_topologicalClosure (hf : FreelyIndependent φ B)
    (hφ : Continuous φ.expectation) {n : ℕ} (hn : 0 < n)
    (label : Fin n → I)
    (halt : ∀ k (hk : k + 1 < n), label ⟨k, by omega⟩ ≠ label ⟨k + 1, hk⟩)
    (x : Fin n → A) (hx : ∀ k, x k ∈ (B (label k)).topologicalClosure) :
    φ.expectation (List.ofFn (fun k => φ.center (x k))).prod = 0 := by
  let F : (Fin n → A) → 𝕜 := fun y => φ.expectation
    (List.ofFn (fun k => φ.center (y k))).prod
  have hc : Continuous φ.center := continuous_id.sub ((continuous_algebraMap 𝕜 A).comp hφ)
  have hF : Continuous F := hφ.comp (by
    simpa only [List.ofFn_eq_map, Function.comp_def] using
      continuous_list_prod (List.finRange n) (fun k _ => hc.comp (continuous_apply k)))
  have hclosed : IsClosed {y | F y = 0} := isClosed_singleton.preimage hF
  have hzero : Set.pi Set.univ (fun k => (B (label k) : Set A)) ⊆ {y | F y = 0} := by
    intro y hy
    let w := List.ofFn (fun k => (label k, φ.center (y k)))
    have hne : w ≠ [] := by
      intro he
      have hl := congrArg List.length he
      simp [w] at hl
      omega
    have hchain : w.IsChain (fun a b => a.1 ≠ b.1) := by
      apply List.isChain_ofFn.mpr
      intro k hk
      exact halt k hk
    have h := hf w hne hchain
      (by
        intro a ha
        obtain ⟨k, rfl⟩ := List.mem_ofFn.mp ha
        exact φ.center_mem _ (hy k (Set.mem_univ k)))
      (by
        intro a ha
        obtain ⟨k, rfl⟩ := List.mem_ofFn.mp ha
        exact φ.expectation_center _)
    change F y = 0
    simpa only [F, w, List.map_ofFn, Function.comp_def] using h
  have hsub := closure_minimal hzero hclosed
  apply hsub
  rw [closure_pi_set]
  exact fun k _ => hx k

/-- A family free for a continuous expectation remains free after taking
actual topological closures of every subalgebra. -/
theorem topologicalClosure (hf : FreelyIndependent φ B)
    (hφ : Continuous φ.expectation) :
    FreelyIndependent φ (fun i => (B i).topologicalClosure) := by
  intro w hw halt hmem hzero
  have hn : 0 < w.length := List.length_pos_iff.mpr hw
  have h := hf.centered_ofFn_topologicalClosure hφ hn (fun k => (w.get k).1)
    (by
      intro k hk
      exact (List.isChain_iff_getElem.mp halt) k hk)
    (fun k => (w.get k).2)
    (fun k => hmem _ (List.get_mem _ _))
  have he : (fun k : Fin w.length => φ.center (w.get k).2) = fun k => (w.get k).2 := by
    funext k
    change (w.get k).2 - algebraMap 𝕜 A (φ.expectation (w.get k).2) = (w.get k).2
    rw [hzero _ (List.get_mem _ _), map_zero, sub_zero]
  rw [he] at h
  rw [List.ofFn_comp' w.get Prod.snd, List.ofFn_get] at h
  exact h
/-- Taking topological closures is equivalent to the original freeness whenever
the expectation is continuous. -/
theorem topologicalClosure_iff (hφ : Continuous φ.expectation) :
    FreelyIndependent φ (fun i => (B i).topologicalClosure) ↔ FreelyIndependent φ B :=
  ⟨fun h => h.mono (fun i => (B i).le_topologicalClosure), fun h => h.topologicalClosure hφ⟩

end FreelyIndependent
end FreeProbability

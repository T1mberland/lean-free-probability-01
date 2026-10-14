import FreeProbability.Algebraic.FreenessClosure
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Actual near-identity inverses in free closed subalgebras

Membership follows from the convergent Neumann series. An arbitrary closed
complex subalgebra is not presumed to contain inverses on the full resolvent set.
-/

namespace FreeProbability
variable {𝕜 A I : Type*} [NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
    [CompleteSpace A]

/-- The actual inverse belongs to the closed subalgebra by its convergent
geometric series whenever the perturbation norm is smaller than one. -/
theorem inverse_one_sub_smul_mem_topologicalClosure (B : Subalgebra 𝕜 A)
    (a : A) (ha : a ∈ B) (z : 𝕜) (hz : ‖z • a‖ < 1) :
    Ring.inverse (1 - z • a) ∈ B.topologicalClosure := by
  have hs := hasSum_geom_series_inverse (z • a) hz
  apply B.isClosed_topologicalClosure.mem_of_tendsto hs
  apply Filter.Eventually.of_forall
  intro s
  apply B.topologicalClosure.sum_mem
  intro k _
  exact B.topologicalClosure.pow_mem (B.le_topologicalClosure (B.smul_mem ha z)) _

namespace FreelyIndependent
variable {φ : ProbabilitySpace 𝕜 A} {B : I → Subalgebra 𝕜 A}

/-- Alternating centered products of actual near-identity inverses vanish for
free variables, using the proved closure extension and convergent inverses. -/
theorem centered_inverse_ofFn_eq_zero (hf : FreelyIndependent φ B)
    (hφ : Continuous φ.expectation) {n : ℕ} (hn : 0 < n)
    (label : Fin n → I)
    (halt : ∀ k (hk : k + 1 < n), label ⟨k, by omega⟩ ≠ label ⟨k + 1, hk⟩)
    (a : Fin n → A) (ha : ∀ k, a k ∈ B (label k)) (z : Fin n → 𝕜)
    (hz : ∀ k, ‖z k • a k‖ < 1) :
    φ.expectation (List.ofFn (fun k => φ.center (Ring.inverse (1 - z k • a k)))).prod = 0 :=
  hf.centered_ofFn_topologicalClosure hφ hn label halt _
    (fun k => inverse_one_sub_smul_mem_topologicalClosure (B (label k)) (a k) (ha k) (z k) (hz k))
end FreelyIndependent
end FreeProbability

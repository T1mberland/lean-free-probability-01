import FreeProbability.Combinatorics.Cumulant
import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Equivalence of all-order moment and cumulant convergence

On each fixed finite word, cumulants are finite polynomials in shorter moments,
and moments are finite polynomials in cumulants. Convergence is along an arbitrary
filter; no norm bound, positivity, or analytic transform assumption is required.
-/

namespace FreeProbability

open Filter Topology

variable {𝕜 X T : Type*} [Field 𝕜] [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜]

/-- Convergence of every moment implies convergence of every recursively inverted cumulant. -/
theorem tendsto_freeCumulant_of_moments (M : T → List X → 𝕜) (L : List X → 𝕜)
    (l : Filter T) (hM : ∀ w, Tendsto (fun t => M t w) l (𝓝 (L w))) (w : List X) :
    Tendsto (fun t => freeCumulant (M t) w) l (𝓝 (freeCumulant L w)) := by
  classical
  suffices ∀ n (w : List X), w.length = n →
    Tendsto (fun t => freeCumulant (M t) w) l (𝓝 (freeCumulant L w)) from this w.length w rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro w hw
    by_cases hnil : w = []
    · subst w
      simpa only [freeCumulant_nil] using (tendsto_const_nhds : Tendsto (fun _ : T => (0 : 𝕜)) l (𝓝 0))
    have hproper : Tendsto (fun t => ∑ p : ProperNoncrossingPartition w.length,
        partitionContribution (freeCumulant (M t)) w p.val) l
        (𝓝 (∑ p : ProperNoncrossingPartition w.length,
          partitionContribution (freeCumulant L) w p.val)) := by
      apply tendsto_finsetSum
      intro p _
      unfold partitionContribution
      apply tendsto_finsetProd
      intro s _
      apply ih (blockWord w s.val).length
      · rw [blockWord_length, ← hw]
        exact p.val.block_card_lt_of_ne_indiscrete p.property s.property
      · rfl
    simpa only [freeCumulant_recursion _ w hnil] using (hM w).sub hproper

/-- Convergence of all cumulants implies moment convergence for normalized moment functions. -/
theorem tendsto_moments_of_freeCumulants (M : T → List X → 𝕜) (L : List X → 𝕜)
    (l : Filter T) (hM0 : ∀ t, M t [] = 1) (hL0 : L [] = 1)
    (hK : ∀ w, Tendsto (fun t => freeCumulant (M t) w) l (𝓝 (freeCumulant L w))) (w : List X) :
    Tendsto (fun t => M t w) l (𝓝 (L w)) := by
  classical
  have h : Tendsto (fun t => ∑ p : NoncrossingPartition w.length,
      partitionContribution (freeCumulant (M t)) w p) l
      (𝓝 (∑ p : NoncrossingPartition w.length, partitionContribution (freeCumulant L) w p)) := by
    apply tendsto_finsetSum
    intro p _
    unfold partitionContribution
    apply tendsto_finsetProd
    intro s _
    exact hK (blockWord w s.val)
  simpa only [← moment_cumulant_formula_all _ hL0 w,
    ← moment_cumulant_formula_all _ (hM0 _) w] using h

/-- All-order moment convergence and cumulant convergence are equivalent. -/
theorem moments_tendsto_iff_freeCumulants (M : T → List X → 𝕜) (L : List X → 𝕜)
    (l : Filter T) (hM0 : ∀ t, M t [] = 1) (hL0 : L [] = 1) :
    (∀ w, Tendsto (fun t => M t w) l (𝓝 (L w))) ↔
      ∀ w, Tendsto (fun t => freeCumulant (M t) w) l (𝓝 (freeCumulant L w)) :=
  ⟨fun h w => tendsto_freeCumulant_of_moments M L l h w,
    fun h w => tendsto_moments_of_freeCumulants M L l hM0 hL0 h w⟩

end FreeProbability

import FreeProbability.Algebraic.CumulantMonochromatic
import FreeProbability.Combinatorics.NoncrossingInterleaveContribution
import FreeProbability.Combinatorics.RefinementMomentCumulant

/-!
# The actual Kreweras moment formula for free alternating products

Freeness removes mixed blocks. The remaining partitions correspond exactly to
pairs `p,q` with `q ≤ K(p)`; summing over the actual refinement interval converts
the second cumulant contribution into the moment contribution of `K(p)`.
This is an algebraic identity, not yet an analytic S-transform theorem.
-/

namespace FreeProbability

open NoncrossingPartition

/-- The original/complementary subalgebra label of a doubled-word position. -/
def parityLabel {n : ℕ} (a : Fin (2 * n)) : Fin 2 := ⟨a.val % 2, Nat.mod_lt _ (by omega)⟩

noncomputable instance parityNoncrossingFintype (n : ℕ) : Fintype (ParityNoncrossing n) :=
  Fintype.ofFinite _

variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]

/-- The mixed moment of an alternating doubled tuple from two free algebras is
its genuine Kreweras sum, including the empty word. -/
theorem FreelyIndependent.expectation_eq_kreweras_sum {φ : ProbabilitySpace 𝕜 A}
    {B : Fin 2 → Subalgebra 𝕜 A} (hfree : FreelyIndependent φ B) {n : ℕ}
    (x : Fin (2 * n) → A) (hmem : ∀ a, x a ∈ B (parityLabel a)) :
    φ.expectation (List.ofFn x).prod =
      ∑ p : NoncrossingPartition n,
        orderedPartitionContribution (cumulant φ) (x ∘ oddOrderEmbedding) p *
          orderedPartitionContribution (fun w => φ.expectation w.prod)
            (x ∘ evenOrderEmbedding) p.kreweras := by
  classical
  have hpar : φ.expectation (List.ofFn x).prod =
      ∑ r : ParityNoncrossing n, orderedPartitionContribution (cumulant φ) x r.val := by
    rw [expectation_eq_sum_orderedCumulants]
    symm
    apply Fintype.sum_of_injective (fun r : ParityNoncrossing n => r.val)
    · exact Subtype.val_injective
    · intro r hr
      have hnot : ¬ r.ParityPreserving := by
        intro hp
        exact hr ⟨⟨r, hp⟩, rfl⟩
      unfold ParityPreserving at hnot
      push Not at hnot
      obtain ⟨a, b, hab, hneq⟩ := hnot
      apply hfree.orderedContribution_eq_zero_of_mixed x parityLabel hmem r
      exact ⟨a, b, hab, fun h => hneq (congrArg Fin.val h)⟩
    · intro _
      rfl
  rw [hpar]
  trans ∑ z : KrewerasCompatiblePairs n,
    orderedPartitionContribution (cumulant φ) (x ∘ oddOrderEmbedding) z.1 *
      orderedPartitionContribution (cumulant φ) (x ∘ evenOrderEmbedding) z.2.val
  · apply Fintype.sum_equiv parityInterleaveEquiv
    intro r
    have he := r.val.interleave_restrict r.property
    rw [← he]
    exact orderedPartitionContribution_interleave _ _ _ _ _
  · rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro p _
    change (∑ q : RefinementsBelow p.kreweras,
      orderedPartitionContribution (cumulant φ) (x ∘ oddOrderEmbedding) p *
        orderedPartitionContribution (cumulant φ) (x ∘ evenOrderEmbedding) q.val) = _
    rw [← Finset.mul_sum]
    congr 1
    exact (orderedMoment_eq_sum_refinementCumulants (fun w => φ.expectation w.prod)
      (by simpa only [List.prod_nil] using φ.map_one) (x ∘ evenOrderEmbedding) p.kreweras).symm

end FreeProbability

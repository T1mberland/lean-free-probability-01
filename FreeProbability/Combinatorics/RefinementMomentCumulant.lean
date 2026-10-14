import FreeProbability.Combinatorics.NoncrossingRefinementBlocks
import FreeProbability.Combinatorics.CumulantNaturality
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Moment–cumulant convolution on the whole refinement lattice

The multiplicative moment of every noncrossing partition is the sum of the
multiplicative cumulant contributions over all finer noncrossing partitions.
The proof uses the actual blockwise refinement equivalence and factorization,
not just the previously known formula at the top partition.
-/

namespace FreeProbability

variable {n : ℕ} {X 𝕜 : Type*} [Field 𝕜]

/-- The lower refinement interval, as a finite summation type. -/
abbrev RefinementsBelow (p : NoncrossingPartition n) := {q : NoncrossingPartition n // q ≤ p}

noncomputable instance (p : NoncrossingPartition n) : Fintype (RefinementsBelow p) := Fintype.ofFinite _

/-- Ordered block words are the tuple given by their increasing block enumeration. -/
theorem orderedBlockWord_ofFn (x : Fin n → X) (s : Finset (Fin n)) :
    orderedBlockWord x s = List.ofFn (x ∘ s.orderEmbOfFin rfl) := by
  rw [List.ofFn_eq_map, ← List.map_map, Finset.listMap_orderEmbOfFin_finRange]
  rfl

/-- The normalized moment–cumulant formula for arbitrary prescribed tuple moments. -/
theorem moment_eq_sum_orderedContributions (M : List X → 𝕜) (h0 : M [] = 1) (x : Fin n → X) :
    M (List.ofFn x) = ∑ p : NoncrossingPartition n, orderedPartitionContribution (freeCumulant M) x p := by
  have h := moment_cumulant_formula_all M h0 (List.ofFn x)
  simp only [← orderedPartitionContribution_get] at h
  exact h.trans (apply_ofFn_get (fun n x => ∑ p : NoncrossingPartition n,
    orderedPartitionContribution (freeCumulant M) x p) x)

/-- The full lower-interval convolution identity in tuple notation. -/
theorem orderedMoment_eq_sum_refinementCumulants (M : List X → 𝕜) (h0 : M [] = 1)
    (x : Fin n → X) (p : NoncrossingPartition n) :
    orderedPartitionContribution M x p = ∑ q : RefinementsBelow p,
      orderedPartitionContribution (freeCumulant M) x q.val := by
  classical
  rw [← p.refinementEquiv.symm.sum_comp (fun q => orderedPartitionContribution (freeCumulant M) x q.val)]
  change orderedPartitionContribution M x p = ∑ R : p.BlockRefinements,
    orderedPartitionContribution (freeCumulant M) x (p.refineBlocks R)
  simp only [orderedPartitionContribution_refineBlocks, Finset.attach_eq_univ]
  rw [← Fintype.prod_sum]
  unfold orderedPartitionContribution
  rw [← Finset.prod_attach p.blocks (fun s => M (orderedBlockWord x s)), Finset.attach_eq_univ]
  apply Finset.prod_congr rfl
  intro s _
  rw [orderedBlockWord_ofFn, moment_eq_sum_orderedContributions M h0]
  rfl

/-- The multiplicative partition moments are the zeta convolution of cumulants
on the actual finite noncrossing refinement lattice. -/
theorem partitionMoment_eq_sum_refinementCumulants (M : List X → 𝕜) (h0 : M [] = 1)
    (w : List X) (p : NoncrossingPartition w.length) :
    partitionContribution M w p = ∑ q : RefinementsBelow p,
      partitionContribution (freeCumulant M) w q.val := by
  simpa only [orderedPartitionContribution_get] using
    orderedMoment_eq_sum_refinementCumulants M h0 w.get p

end FreeProbability

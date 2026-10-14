import FreeProbability.Combinatorics.CoveringAdjacentSums
import FreeProbability.Algebraic.CumulantUnit

/-!
# Adjacent-product cumulant formula

Multiplying two adjacent coordinates sums the original partition contributions
over the fiber that becomes the one-block partition after joining the selected
adjacent pair. The proof groups all noncrossing partitions into contraction
fibers and applies all-order induction to proper distinguished blocks.
-/

namespace FreeProbability

variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A] {n : ℕ}

omit [Algebra 𝕜 A] in
private theorem outside_duplicate_product (K : List A → 𝕜) (x : Fin (n + 1) → A)
    (q : NoncrossingPartition n) (i : Fin n) (s : Finset (Fin n)) (hs : s ∈ q.blocks) (hi : i ∈ s) :
    (∏ t ∈ (q.duplicate i).blocks.erase (NoncrossingPartition.duplicateBlock i s),
      K (orderedBlockWord x t)) =
      ∏ t ∈ q.blocks.erase s, K (orderedBlockWord (fuseAdjacent x i) t) := by
  classical
  rw [q.blocks_duplicate, ← Finset.image_erase (NoncrossingPartition.duplicateBlock_injective i),
    Finset.prod_image]
  · apply Finset.prod_congr rfl
    intro t ht
    obtain ⟨hts, ht⟩ := Finset.mem_erase.mp ht
    apply congrArg K
    exact NoncrossingPartition.orderedBlockWord_duplicateBlock_of_not_mem x i t
      (q.not_mem_block_of_mem_other ht hs hts hi)
  · exact fun _ _ _ _ h => NoncrossingPartition.duplicateBlock_injective i h

private theorem proper_adjacent_fiber (φ : ProbabilitySpace 𝕜 A)
    (x : Fin (n + 1) → A) (i : Fin n)
    (ih : ∀ m < n, ∀ (y : Fin (m + 1) → A) (j : Fin m),
      cumulant φ (List.ofFn (fuseAdjacent y j)) =
        ∑ p : AdjacentPartitionFiber (⊤ : NoncrossingPartition (m + 1)) j,
          orderedPartitionContribution (cumulant φ) y p.val)
    (q : NoncrossingPartition n) (hq : q ≠ ⊤) :
    (∑ p : AdjacentPartitionFiber (q.duplicate i) i,
      orderedPartitionContribution (cumulant φ) x p.val) =
        orderedPartitionContribution (cumulant φ) (fuseAdjacent x i) q := by
  classical
  obtain ⟨s, ⟨hs, his⟩, _⟩ := q.existsUnique_block i
  have hdup := q.duplicateBlock_mem_blocks i hs
  have hl : i.castSucc ∈ NoncrossingPartition.duplicateBlock i s := by
    simpa only [NoncrossingPartition.mem_duplicateBlock, Fin.predAbove_castSucc_self] using his
  have hr : i.succ ∈ NoncrossingPartition.duplicateBlock i s := by
    simpa only [NoncrossingPartition.mem_duplicateBlock, Fin.predAbove_succ_self] using his
  rw [sum_adjacentPartitionFiber_contribution _ _ _ _ _ hdup hl hr,
    outside_duplicate_product _ _ q i s hs his,
    sum_duplicateBlock_covering_eq_adjacentTop _ _ i s his hl hr]
  have hlt : s.card < n := q.block_card_lt_of_ne_indiscrete
    (by simpa only [NoncrossingPartition.top_eq_indiscrete] using hq) hs
  rw [← ih s.card hlt]
  rw [orderedBlockWord_fuseAdjacent_of_mem]
  unfold orderedPartitionContribution
  rw [← Finset.mul_prod_erase q.blocks _ hs]
  exact mul_comm _ _

/-- The all-order adjacent-product formula over the genuine noncrossing top join fiber. -/
theorem cumulant_fuseAdjacent (φ : ProbabilitySpace 𝕜 A) (x : Fin (n + 1) → A) (i : Fin n) :
    cumulant φ (List.ofFn (fuseAdjacent x i)) =
      ∑ p : AdjacentPartitionFiber (⊤ : NoncrossingPartition (n + 1)) i,
        orderedPartitionContribution (cumulant φ) x p.val := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
    have htop : orderedPartitionContribution (cumulant φ) (fuseAdjacent x i)
        (⊤ : NoncrossingPartition n) = cumulant φ (List.ofFn (fuseAdjacent x i)) := by
      rw [NoncrossingPartition.top_eq_indiscrete]
      exact orderedPartitionContribution_indiscrete φ _ hn
    have hdup : (⊤ : NoncrossingPartition n).duplicate i = ⊤ := by
      apply Subtype.ext
      apply Setoid.ext
      intro a b
      have ht0 : (⊤ : NoncrossingPartition n).val = (⊤ : Setoid (Fin n)) :=
        congrArg Subtype.val NoncrossingPartition.top_eq_indiscrete
      have ht1 : (⊤ : NoncrossingPartition (n + 1)).val = (⊤ : Setoid (Fin (n + 1))) :=
        congrArg Subtype.val NoncrossingPartition.top_eq_indiscrete
      rw [NoncrossingPartition.duplicate_rel, ht0, ht1]
      rfl
    have hred := expectation_eq_sum_orderedCumulants φ (fuseAdjacent x i)
    rw [Fintype.sum_eq_add_sum_subtype_ne _ (⊤ : NoncrossingPartition n), htop] at hred
    have horig := expectation_eq_sum_orderedCumulants φ x
    rw [sum_orderedPartitionContribution_adjacentFibers _ _ i,
      Fintype.sum_eq_add_sum_subtype_ne _ (⊤ : NoncrossingPartition n), hdup] at horig
    have hproper :
        (∑ q : {q : NoncrossingPartition n // q ≠ ⊤},
          ∑ p : AdjacentPartitionFiber (q.val.duplicate i) i,
            orderedPartitionContribution (cumulant φ) x p.val) =
        ∑ q : {q : NoncrossingPartition n // q ≠ ⊤},
          orderedPartitionContribution (cumulant φ) (fuseAdjacent x i) q.val := by
      apply Finset.sum_congr rfl
      intro q _
      exact proper_adjacent_fiber φ x i ih q.val q.property
    have hm := congrArg φ.expectation (prod_ofFn_fuseAdjacent x i)
    rw [hred, horig, hproper] at hm
    exact add_right_cancel hm

end FreeProbability

import FreeProbability.Algebraic.CumulantAdjacentProduct

/-! # Adjacent-product identities at every noncrossing partition -/

namespace FreeProbability

variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A] {n : ℕ}

omit [Algebra 𝕜 A] in
private theorem outside_product (K : List A → 𝕜) (x : Fin (n + 1) → A)
    (q : NoncrossingPartition n) (i : Fin n) (s : Finset (Fin n)) (hs : s ∈ q.blocks) (hi : i ∈ s) :
    (∏ t ∈ (q.duplicate i).blocks.erase (NoncrossingPartition.duplicateBlock i s), K (orderedBlockWord x t)) =
      ∏ t ∈ q.blocks.erase s, K (orderedBlockWord (fuseAdjacent x i) t) := by
  classical
  rw [q.blocks_duplicate, ← Finset.image_erase (NoncrossingPartition.duplicateBlock_injective i), Finset.prod_image]
  · apply Finset.prod_congr rfl
    intro t ht
    obtain ⟨hts, ht⟩ := Finset.mem_erase.mp ht
    exact congrArg K (NoncrossingPartition.orderedBlockWord_duplicateBlock_of_not_mem x i t
      (q.not_mem_block_of_mem_other ht hs hts hi))
  · exact fun _ _ _ _ h => NoncrossingPartition.duplicateBlock_injective i h

/-- Every adjacent-product partition contribution is the full contribution sum
of its contraction fiber, not just the top-partition cumulant. -/
theorem orderedCumulantContribution_fuseAdjacent (φ : ProbabilitySpace 𝕜 A)
    (x : Fin (n + 1) → A) (i : Fin n) (q : NoncrossingPartition n) :
    orderedPartitionContribution (cumulant φ) (fuseAdjacent x i) q =
      ∑ p : AdjacentPartitionFiber (q.duplicate i) i,
        orderedPartitionContribution (cumulant φ) x p.val := by
  classical
  symm
  obtain ⟨s, ⟨hs, his⟩, _⟩ := q.existsUnique_block i
  have hdup := q.duplicateBlock_mem_blocks i hs
  have hl : i.castSucc ∈ NoncrossingPartition.duplicateBlock i s := by
    simpa only [NoncrossingPartition.mem_duplicateBlock, Fin.predAbove_castSucc_self] using his
  have hr : i.succ ∈ NoncrossingPartition.duplicateBlock i s := by
    simpa only [NoncrossingPartition.mem_duplicateBlock, Fin.predAbove_succ_self] using his
  rw [sum_adjacentPartitionFiber_contribution _ _ _ _ _ hdup hl hr,
    outside_product _ _ q i s hs his,
    sum_duplicateBlock_covering_eq_adjacentTop _ _ i s his hl hr,
    ← cumulant_fuseAdjacent, orderedBlockWord_fuseAdjacent_of_mem]
  unfold orderedPartitionContribution
  rw [← Finset.mul_prod_erase q.blocks _ hs]
  exact mul_comm _ _

noncomputable instance contractionFiberFintype (q : NoncrossingPartition n) (i : Fin n) :
    Fintype {p : NoncrossingPartition (n + 1) // p.contract i = q} := Fintype.ofFinite _

/-- The same all-partition identity stated directly with quotient fibers. -/
theorem orderedCumulantContribution_fuseAdjacent_contract (φ : ProbabilitySpace 𝕜 A)
    (x : Fin (n + 1) → A) (i : Fin n) (q : NoncrossingPartition n) :
    orderedPartitionContribution (cumulant φ) (fuseAdjacent x i) q =
      ∑ p : {p : NoncrossingPartition (n + 1) // p.contract i = q},
        orderedPartitionContribution (cumulant φ) x p.val := by
  classical
  rw [orderedCumulantContribution_fuseAdjacent]
  symm
  exact Fintype.sum_equiv (NoncrossingPartition.contractionFiberEquiv q i) _ _ (fun _ => rfl)

end FreeProbability

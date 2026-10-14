import FreeProbability.Combinatorics.DuplicateBlockEnumeration
import FreeProbability.Combinatorics.AdjacentContributionGrouping

/-! # Reindexing local covering sums as top adjacent-product fibers -/

namespace FreeProbability

variable {n : ℕ}

/-- Adjacent marked-point covering is exactly the top join fiber. -/
def pointCoveringAdjacentEquiv (i : Fin n) :
    PointCoveringPartitions i.castSucc i.succ ≃
      AdjacentPartitionFiber (⊤ : NoncrossingPartition (n + 1)) i where
  toFun p := ⟨p.val, (p.val.sup_adjacentPair_eq_top_iff i).mpr p.property⟩
  invFun p := ⟨p.val, (p.val.sup_adjacentPair_eq_top_iff i).mp p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact equivalence of the two top-fiber sum presentations. -/
theorem sum_pointCovering_eq_adjacentTop {X 𝕜 : Type*} [CommSemiring 𝕜]
    (K : List X → 𝕜) (x : Fin (n + 1) → X) (i : Fin n) :
    (∑ p : PointCoveringPartitions i.castSucc i.succ, orderedPartitionContribution K x p.val) =
      ∑ p : AdjacentPartitionFiber (⊤ : NoncrossingPartition (n + 1)) i,
        orderedPartitionContribution K x p.val := by
  classical
  exact Fintype.sum_equiv (pointCoveringAdjacentEquiv i) _ _ (fun _ => rfl)

/-- The local covering sum of the duplicated distinguished block is a top adjacent
fiber sum for the explicit local inserted-letter tuple. -/
theorem sum_duplicateBlock_covering_eq_adjacentTop {X 𝕜 : Type*} [CommSemiring 𝕜]
    (K : List X → 𝕜) (x : Fin (n + 1) → X) (i : Fin n)
    (s : Finset (Fin n)) (hi : i ∈ s)
    (hl : i.castSucc ∈ NoncrossingPartition.duplicateBlock i s)
    (hr : i.succ ∈ NoncrossingPartition.duplicateBlock i s) :
    (∑ p : PairCoveringPartitions (NoncrossingPartition.duplicateBlock i s) i hl hr,
      orderedPartitionContribution K (x ∘ (NoncrossingPartition.duplicateBlock i s).orderEmbOfFin rfl) p.val) =
      ∑ p : AdjacentPartitionFiber (⊤ : NoncrossingPartition (s.card + 1))
          ((s.orderIsoOfFin rfl).symm ⟨i, hi⟩),
        orderedPartitionContribution K
          (((s.orderIsoOfFin rfl).symm ⟨i, hi⟩).castSucc.insertNth
            (x i.castSucc) (fun a => x (i.castSucc.succAbove (s.orderEmbOfFin rfl a)))) p.val := by
  classical
  have hcard : (NoncrossingPartition.duplicateBlock i s).card = s.card + 1 := by
    simp only [NoncrossingPartition.card_duplicateBlock, hi, ite_true]
  have h := sum_pointCoveringPartitionContribution_reindex K
    (x ∘ (NoncrossingPartition.duplicateBlock i s).orderEmbOfFin rfl)
    (((NoncrossingPartition.duplicateBlock i s).orderIsoOfFin rfl).symm ⟨i.castSucc, hl⟩)
    (((NoncrossingPartition.duplicateBlock i s).orderIsoOfFin rfl).symm ⟨i.succ, hr⟩)
    (Fin.castOrderIso hcard.symm)
  rw [duplicateBlock_left_index i s hi hcard hl,
    duplicateBlock_right_index i s hi hcard hr, duplicateBlock_tuple_reindex x i s hi hcard,
    sum_pointCovering_eq_adjacentTop] at h
  exact h

end FreeProbability

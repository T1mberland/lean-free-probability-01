import FreeProbability.Combinatorics.NoncrossingAdjacentFiber

/-! # Grouping the moment–cumulant sum by adjacent contraction -/

namespace FreeProbability.NoncrossingPartition

variable {n : ℕ}

/-- The quotient fiber is the corresponding adjacent-join fiber of the duplicated partition. -/
theorem contract_eq_iff (p : NoncrossingPartition (n + 1)) (q : NoncrossingPartition n)
    (i : Fin n) : p.contract i = q ↔ p ⊔ adjacentPair i = q.duplicate i := by
  constructor
  · intro h
    rw [← p.duplicate_contract i, h]
  · intro h
    apply le_antisymm
    · apply (duplicate_le_duplicate_iff _ _ i).mp
      rw [duplicate_contract, h]
    · apply (duplicate_le_duplicate_iff _ _ i).mp
      rw [duplicate_contract, h]

/-- Exact reindexing from contraction fibers to adjacent-join fibers. -/
def contractionFiberEquiv (q : NoncrossingPartition n) (i : Fin n) :
    {p : NoncrossingPartition (n + 1) // p.contract i = q} ≃
      AdjacentPartitionFiber (q.duplicate i) i where
  toFun p := ⟨p.val, (p.val.contract_eq_iff q i).mp p.property⟩
  invFun p := ⟨p.val, (p.val.contract_eq_iff q i).mpr p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

end FreeProbability.NoncrossingPartition

namespace FreeProbability

variable {n : ℕ} {X 𝕜 : Type*} [CommSemiring 𝕜]

/-- The full original partition sum is the sum of the adjacent-product fibers,
indexed by the reduced noncrossing partitions. -/
theorem sum_orderedPartitionContribution_adjacentFibers (K : List X → 𝕜)
    (x : Fin (n + 1) → X) (i : Fin n) :
    (∑ p : NoncrossingPartition (n + 1), orderedPartitionContribution K x p) =
      ∑ q : NoncrossingPartition n, ∑ p : AdjacentPartitionFiber (q.duplicate i) i,
        orderedPartitionContribution K x p.val := by
  classical
  have h := Fintype.sum_fiberwise (fun p : NoncrossingPartition (n + 1) => p.contract i)
    (fun p => orderedPartitionContribution K x p)
  rw [← h]
  apply Finset.sum_congr rfl
  intro q _
  exact Fintype.sum_equiv (NoncrossingPartition.contractionFiberEquiv q i)
    _ _ (fun _ => rfl)

end FreeProbability

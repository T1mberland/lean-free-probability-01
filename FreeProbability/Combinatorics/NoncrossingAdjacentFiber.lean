import FreeProbability.Combinatorics.NoncrossingAdjacentMerge
import FreeProbability.Combinatorics.BlockRefinementContribution

/-!
# Local decomposition of adjacent-contraction fibers

For a partition containing a specified adjacent pair, only its block containing
the pair can change before the pair is joined. The fiber is exactly the local
noncrossing partitions of that block whose classes all meet one of the two
selected positions. All other blocks stay fixed.
-/

namespace FreeProbability.NoncrossingPartition

variable {n : ℕ}

private theorem position_index (s : Finset (Fin (n + 1))) (a : Fin (n + 1)) (ha : a ∈ s) :
    s.orderEmbOfFin rfl ((s.orderIsoOfFin rfl).symm ⟨a, ha⟩) = a := by
  exact congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨a, ha⟩)

/-- The local partitions whose classes all meet one of the two marked positions. -/
def CoversPair (s : Finset (Fin (n + 1))) (i : Fin n)
    (hl : i.castSucc ∈ s) (hr : i.succ ∈ s) (r : NoncrossingPartition s.card) : Prop :=
  ∀ a, r.val.r a ((s.orderIsoOfFin rfl).symm ⟨i.castSucc, hl⟩) ∨
    r.val.r a ((s.orderIsoOfFin rfl).symm ⟨i.succ, hr⟩)

/-- Restriction sends an adjacent-product fiber to its covering local partition. -/
theorem coversPair_restrict_of_join (p q : NoncrossingPartition (n + 1))
    (i : Fin n) (hpq : p ⊔ adjacentPair i = q)
    (s : Finset (Fin (n + 1))) (hs : s ∈ q.blocks)
    (hl : i.castSucc ∈ s) (hr : i.succ ∈ s) :
    CoversPair s i hl hr (p.restrict (s.orderEmbOfFin rfl)) := by
  intro a
  have h : q.val.r (s.orderEmbOfFin rfl a) i.castSucc :=
    (q.same_block_iff _ _).mp ⟨s, hs, s.orderEmbOfFin_mem rfl a, hl⟩
  rw [← hpq, ← mergeAdjacent_eq_sup] at h
  have ha : p.val.r (s.orderEmbOfFin rfl a) i.castSucc ∨
      p.val.r (s.orderEmbOfFin rfl a) i.succ := by
    rcases h with h | ⟨ha, _⟩
    · exact Or.inl h
    · exact ha
  change p.val.r (s.orderEmbOfFin rfl a)
    (s.orderEmbOfFin rfl ((s.orderIsoOfFin rfl).symm ⟨i.castSucc, hl⟩)) ∨
    p.val.r (s.orderEmbOfFin rfl a)
    (s.orderEmbOfFin rfl ((s.orderIsoOfFin rfl).symm ⟨i.succ, hr⟩))
  simpa only [position_index] using ha

/-- Refining the distinguished block by a covering local partition lies in the fiber. -/
theorem refineBlock_join_eq_of_coversPair (q : NoncrossingPartition (n + 1))
    (i : Fin n) (s : Finset (Fin (n + 1))) (hs : s ∈ q.blocks)
    (hl : i.castSucc ∈ s) (hr : i.succ ∈ s) (r : NoncrossingPartition s.card)
    (hcover : CoversPair s i hl hr r) : q.refineBlock s hs r ⊔ adjacentPair i = q := by
  apply le_antisymm
  · exact sup_le (q.refineBlock_le s hs r) ((adjacentPair_le_iff q i).mpr
      ((q.same_block_iff _ _).mp ⟨s, hs, hl, hr⟩))
  · rw [← mergeAdjacent_eq_sup]
    intro a b hab
    by_cases ha : a ∈ s
    · have hb : b ∈ s := (q.rel_iff_mem_block hs ha b).mp hab
      have hanchors (a : Fin (n + 1)) (ha : a ∈ s) :
          (q.refineBlock s hs r).val.r a i.castSucc ∨
          (q.refineBlock s hs r).val.r a i.succ := by
        rcases hcover ((s.orderIsoOfFin rfl).symm ⟨a, ha⟩) with h | h
        · exact Or.inl ((q.refineBlock_rel_inside s hs r a i.castSucc ha hl).mpr h)
        · exact Or.inr ((q.refineBlock_rel_inside s hs r a i.succ ha hr).mpr h)
      exact Or.inr ⟨hanchors a ha, hanchors b hb⟩
    · exact Or.inl ((q.refineBlock_rel_of_not_mem s hs r a b ha).mpr hab)

private theorem rel_of_join_outside (p q : NoncrossingPartition (n + 1))
    (i : Fin n) (hpq : p ⊔ adjacentPair i = q)
    (s : Finset (Fin (n + 1))) (hs : s ∈ q.blocks) (hl : i.castSucc ∈ s)
    (hr : i.succ ∈ s) (a b : Fin (n + 1)) (ha : a ∉ s) (hab : q.val.r a b) :
    p.val.r a b := by
  have hle : p ≤ q := hpq ▸ le_sup_left
  rw [← hpq, ← mergeAdjacent_eq_sup] at hab
  rcases hab with h | ⟨hanchor, _⟩
  · exact h
  · rcases hanchor with h | h
    · exact False.elim (ha ((q.rel_iff_mem_block hs hl a).mp (q.val.symm (hle h))))
    · exact False.elim (ha ((q.rel_iff_mem_block hs hr a).mp (q.val.symm (hle h))))

/-- The original partition in a fiber is recovered by refining only the distinguished block. -/
theorem refineBlock_restrict_of_join (p q : NoncrossingPartition (n + 1))
    (i : Fin n) (hpq : p ⊔ adjacentPair i = q)
    (s : Finset (Fin (n + 1))) (hs : s ∈ q.blocks)
    (hl : i.castSucc ∈ s) (hr : i.succ ∈ s) :
    q.refineBlock s hs (p.restrict (s.orderEmbOfFin rfl)) = p := by
  have hle : p ≤ q := hpq ▸ le_sup_left
  apply Subtype.ext
  apply Setoid.ext
  intro a b
  constructor
  · intro h
    by_cases ha : a ∈ s
    · have hb : b ∈ s := (q.rel_iff_mem_block hs ha b).mp h.1
      have hlocal := h.2 ha hb
      change p.val.r (s.orderEmbOfFin rfl ((s.orderIsoOfFin rfl).symm ⟨a, ha⟩))
        (s.orderEmbOfFin rfl ((s.orderIsoOfFin rfl).symm ⟨b, hb⟩)) at hlocal
      simpa only [position_index] using hlocal
    · exact rel_of_join_outside p q i hpq s hs hl hr a b ha h.1
  · intro h
    refine ⟨hle h, ?_⟩
    intro ha hb
    change p.val.r (s.orderEmbOfFin rfl ((s.orderIsoOfFin rfl).symm ⟨a, ha⟩))
      (s.orderEmbOfFin rfl ((s.orderIsoOfFin rfl).symm ⟨b, hb⟩))
    simpa only [position_index] using h

/-- Exact bijection between a global adjacent-product fiber and the local covering partitions. -/
def adjacentFiberEquiv (q : NoncrossingPartition (n + 1)) (i : Fin n)
    (s : Finset (Fin (n + 1))) (hs : s ∈ q.blocks) (hl : i.castSucc ∈ s) (hr : i.succ ∈ s) :
    {p : NoncrossingPartition (n + 1) // p ⊔ adjacentPair i = q} ≃
      {r : NoncrossingPartition s.card // CoversPair s i hl hr r} where
  toFun p := ⟨p.val.restrict (s.orderEmbOfFin rfl),
    coversPair_restrict_of_join p.val q i p.property s hs hl hr⟩
  invFun r := ⟨q.refineBlock s hs r.val,
    refineBlock_join_eq_of_coversPair q i s hs hl hr r.val r.property⟩
  left_inv p := Subtype.ext (refineBlock_restrict_of_join p.val q i p.property s hs hl hr)
  right_inv r := Subtype.ext (q.restrict_refineBlock s hs r.val)

end FreeProbability.NoncrossingPartition

namespace FreeProbability

variable {n : ℕ}

/-- A fiber of joining with the selected adjacent pair. -/
abbrev AdjacentPartitionFiber (q : NoncrossingPartition (n + 1)) (i : Fin n) :=
  {p : NoncrossingPartition (n + 1) // p ⊔ NoncrossingPartition.adjacentPair i = q}

noncomputable instance (q : NoncrossingPartition (n + 1)) (i : Fin n) :
    Fintype (AdjacentPartitionFiber q i) := Fintype.ofFinite _

/-- Local partitions in which every class meets one of the marked positions. -/
abbrev PairCoveringPartitions (s : Finset (Fin (n + 1))) (i : Fin n)
    (hl : i.castSucc ∈ s) (hr : i.succ ∈ s) :=
  {r : NoncrossingPartition s.card // NoncrossingPartition.CoversPair s i hl hr r}

noncomputable instance (s : Finset (Fin (n + 1))) (i : Fin n)
    (hl : i.castSucc ∈ s) (hr : i.succ ∈ s) : Fintype (PairCoveringPartitions s i hl hr) :=
  Fintype.ofFinite _

/-- Exact partition-contribution factorization for an adjacent-product fiber. -/
theorem sum_adjacentPartitionFiber_contribution {X 𝕜 : Type*} [CommSemiring 𝕜]
    (K : List X → 𝕜) (x : Fin (n + 1) → X)
    (q : NoncrossingPartition (n + 1)) (i : Fin n)
    (s : Finset (Fin (n + 1))) (hs : s ∈ q.blocks) (hl : i.castSucc ∈ s) (hr : i.succ ∈ s) :
    (∑ p : AdjacentPartitionFiber q i, orderedPartitionContribution K x p.val) =
      (∏ t ∈ q.blocks.erase s, K (orderedBlockWord x t)) *
        ∑ r : PairCoveringPartitions s i hl hr,
          orderedPartitionContribution K (x ∘ s.orderEmbOfFin rfl) r.val := by
  classical
  rw [← (NoncrossingPartition.adjacentFiberEquiv q i s hs hl hr).symm.sum_comp
    (fun p => orderedPartitionContribution K x p.val)]
  change (∑ r : PairCoveringPartitions s i hl hr,
    orderedPartitionContribution K x (q.refineBlock s hs r.val)) = _
  simp only [orderedPartitionContribution_refineBlock, Finset.mul_sum]

end FreeProbability

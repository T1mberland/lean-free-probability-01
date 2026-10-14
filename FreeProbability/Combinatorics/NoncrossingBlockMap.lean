import FreeProbability.Combinatorics.NoncrossingRestriction

/-! # Actual block maps and strict refinement cardinality -/

namespace FreeProbability.NoncrossingPartition

variable {n : ℕ}

/-- The unique actual block containing a prescribed position. -/
noncomputable def blockOf (p : NoncrossingPartition n) (a : Fin n) : {s // s ∈ p.blocks} :=
  ⟨Classical.choose (p.existsUnique_block a), (Classical.choose_spec (p.existsUnique_block a)).1.1⟩

theorem mem_blockOf (p : NoncrossingPartition n) (a : Fin n) : a ∈ (p.blockOf a).val :=
  (Classical.choose_spec (p.existsUnique_block a)).1.2

/-- Equality of actual containing blocks is exactly the partition relation. -/
theorem blockOf_eq_iff (p : NoncrossingPartition n) (a b : Fin n) :
    p.blockOf a = p.blockOf b ↔ p.val.r a b := by
  constructor
  · intro h
    apply (p.same_block_iff a b).mp
    refine ⟨(p.blockOf a).val, (p.blockOf a).property, p.mem_blockOf a, ?_⟩
    rw [h]
    exact p.mem_blockOf b
  · intro h
    apply Subtype.ext
    exact (p.existsUnique_block b).unique
      ⟨(p.blockOf a).property, (p.rel_iff_mem_block (p.blockOf a).property (p.mem_blockOf a) b).mp h⟩
      ⟨(p.blockOf b).property, p.mem_blockOf b⟩

/-- Refinement maps each fine block to its unique containing coarse block. -/
noncomputable def refinementBlockMap {p q : NoncrossingPartition n} (hpq : p ≤ q)
    (s : {s // s ∈ p.blocks}) : {t // t ∈ q.blocks} :=
  ⟨Classical.choose (block_subset_block_of_le hpq s.property),
    (Classical.choose_spec (block_subset_block_of_le hpq s.property)).1⟩

theorem refinementBlockMap_subset {p q : NoncrossingPartition n} (hpq : p ≤ q)
    (s : {s // s ∈ p.blocks}) : s.val ⊆ (refinementBlockMap hpq s).val :=
  (Classical.choose_spec (block_subset_block_of_le hpq s.property)).2

@[simp] theorem refinementBlockMap_blockOf {p q : NoncrossingPartition n}
    (hpq : p ≤ q) (a : Fin n) : refinementBlockMap hpq (p.blockOf a) = q.blockOf a := by
  apply Subtype.ext
  exact (q.existsUnique_block a).unique
    ⟨(refinementBlockMap hpq (p.blockOf a)).property,
      refinementBlockMap_subset hpq _ (p.mem_blockOf a)⟩
    ⟨(q.blockOf a).property, q.mem_blockOf a⟩

theorem refinementBlockMap_surjective {p q : NoncrossingPartition n} (hpq : p ≤ q) :
    Function.Surjective (refinementBlockMap hpq) := by
  intro t
  obtain ⟨a, ha⟩ := q.block_nonempty t.property
  refine ⟨p.blockOf a, ?_⟩
  rw [refinementBlockMap_blockOf]
  apply Subtype.ext
  exact (q.existsUnique_block a).unique ⟨(q.blockOf a).property, q.mem_blockOf a⟩ ⟨t.property, ha⟩

/-- Coarsening cannot increase the number of actual blocks. -/
theorem card_blocks_antitone {p q : NoncrossingPartition n} (hpq : p ≤ q) :
    q.blocks.card ≤ p.blocks.card := by
  classical
  simpa only [Fintype.card_coe] using
    Fintype.card_le_of_surjective (refinementBlockMap hpq) (refinementBlockMap_surjective hpq)

/-- A refinement with the same number of blocks is the identical partition. -/
theorem eq_of_le_of_card_blocks_eq {p q : NoncrossingPartition n} (hpq : p ≤ q)
    (hc : p.blocks.card = q.blocks.card) : p = q := by
  classical
  let e : {s // s ∈ p.blocks} ≃ {s // s ∈ q.blocks} := Fintype.equivOfCardEq (by simpa using hc)
  have hi : Function.Injective (refinementBlockMap hpq) :=
    (Finite.injective_iff_surjective_of_equiv e).mpr (refinementBlockMap_surjective hpq)
  apply le_antisymm hpq
  intro a b hab
  apply (p.blockOf_eq_iff a b).mp
  apply hi
  simpa only [refinementBlockMap_blockOf] using (q.blockOf_eq_iff a b).mpr hab

/-- Every proper refinement strictly increases the number of actual blocks. -/
theorem card_blocks_lt_of_lt {p q : NoncrossingPartition n} (hpq : p < q) :
    q.blocks.card < p.blocks.card := by
  have hle := card_blocks_antitone hpq.le
  apply lt_of_le_of_ne hle
  intro he
  exact hpq.ne (eq_of_le_of_card_blocks_eq hpq.le he.symm)

end FreeProbability.NoncrossingPartition

import FreeProbability.Combinatorics.NoncrossingSingletonInsertion
import Mathlib.Data.Finset.Sort

/-!
# Restriction and refinement of noncrossing partitions

Restriction along an order embedding preserves noncrossing. Its actual blocks
are precisely the nonempty pullbacks of the original blocks. Refinement is
characterized by containment of every finer block in a coarser block.
-/

namespace FreeProbability.NoncrossingPartition

variable {m n : ℕ}

/-- Restrict a noncrossing partition along an order embedding. -/
def restrict (p : NoncrossingPartition n) (f : Fin m ↪o Fin n) :
    NoncrossingPartition m := ⟨Setoid.comap f p.val, p.property.comap f⟩

/-- The positions of a block retained by an order embedding. -/
noncomputable def pullbackBlock (f : Fin m ↪o Fin n) (s : Finset (Fin n)) : Finset (Fin m) :=
  Finset.univ.filter (fun i => f i ∈ s)

@[simp] theorem mem_pullbackBlock (f : Fin m ↪o Fin n) (s : Finset (Fin n)) (i : Fin m) :
    i ∈ pullbackBlock f s ↔ f i ∈ s := by
  classical
  simp [pullbackBlock]

/-- Every nonempty pullback of a block is a block of the restricted partition. -/
theorem pullback_mem_blocks_restrict (p : NoncrossingPartition n) (f : Fin m ↪o Fin n)
    {s : Finset (Fin n)} (hs : s ∈ p.blocks) (hne : (pullbackBlock f s).Nonempty) :
    pullbackBlock f s ∈ (p.restrict f).blocks := by
  classical
  obtain ⟨a, ha⟩ := hne
  obtain ⟨t, ⟨ht, hat⟩, _⟩ := (p.restrict f).existsUnique_block a
  have he : t = pullbackBlock f s := by
    ext b
    rw [← (p.restrict f).rel_iff_mem_block ht hat b, mem_pullbackBlock]
    exact p.rel_iff_mem_block hs ((mem_pullbackBlock f s a).mp ha) (f b)
  exact he ▸ ht

/-- No other blocks occur after restriction. -/
theorem blocks_restrict (p : NoncrossingPartition n) (f : Fin m ↪o Fin n) :
    (p.restrict f).blocks =
      (p.blocks.filter (fun s => (pullbackBlock f s).Nonempty)).image (pullbackBlock f) := by
  classical
  ext t
  rw [Finset.mem_image]
  constructor
  · intro ht
    obtain ⟨a, hat⟩ := (p.restrict f).block_nonempty ht
    obtain ⟨s, ⟨hs, hfs⟩, _⟩ := p.existsUnique_block (f a)
    have ha : a ∈ pullbackBlock f s := (mem_pullbackBlock f s a).mpr hfs
    have hb := p.pullback_mem_blocks_restrict f hs ⟨a, ha⟩
    have he : pullbackBlock f s = t :=
      ((p.restrict f).existsUnique_block a).unique ⟨hb, ha⟩ ⟨ht, hat⟩
    exact ⟨s, Finset.mem_filter.mpr ⟨hs, ⟨a, ha⟩⟩, he⟩
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨hs, hne⟩ := Finset.mem_filter.mp hs
    exact p.pullback_mem_blocks_restrict f hs hne

/-- Restricting to the positions of one of its own blocks gives the single-block partition. -/
theorem restrict_block_eq_indiscrete (p : NoncrossingPartition n)
    {s : Finset (Fin n)} (hs : s ∈ p.blocks) :
    p.restrict (s.orderEmbOfFin rfl) = indiscrete s.card := by
  apply Subtype.ext
  apply Setoid.ext
  intro a b
  constructor
  · intro _
    trivial
  · intro _
    exact (p.same_block_iff _ _).mp ⟨s, hs, s.orderEmbOfFin_mem rfl a,
      s.orderEmbOfFin_mem rfl b⟩

/-- Every block of a finer partition lies in a block of the coarser partition. -/
theorem block_subset_block_of_le {p q : NoncrossingPartition n} (hpq : p ≤ q)
    {s : Finset (Fin n)} (hs : s ∈ p.blocks) : ∃ t ∈ q.blocks, s ⊆ t := by
  obtain ⟨a, ha⟩ := p.block_nonempty hs
  obtain ⟨t, ⟨ht, hat⟩, _⟩ := q.existsUnique_block a
  refine ⟨t, ht, ?_⟩
  intro b hb
  exact (q.rel_iff_mem_block ht hat b).mp (hpq ((p.rel_iff_mem_block hs ha b).mpr hb))

/-- Block containment is exactly refinement. -/
theorem le_iff_block_subset (p q : NoncrossingPartition n) :
    p ≤ q ↔ ∀ s ∈ p.blocks, ∃ t ∈ q.blocks, s ⊆ t := by
  constructor
  · intro h s hs
    exact block_subset_block_of_le h hs
  · intro h a b hab
    obtain ⟨s, hs, has, hbs⟩ := (p.same_block_iff a b).mpr hab
    obtain ⟨t, ht, hst⟩ := h s hs
    exact (q.same_block_iff a b).mp ⟨t, ht, hst has, hst hbs⟩

/-- A block wholly in the range is recovered by taking the image of its pullback. -/
theorem image_pullbackBlock (f : Fin m ↪o Fin n) (s : Finset (Fin n))
    (hs : ∀ b ∈ s, b ∈ Set.range f) : (pullbackBlock f s).image f = s := by
  classical
  ext b
  constructor
  · intro hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    exact (mem_pullbackBlock f s a).mp ha
  · intro hb
    obtain ⟨a, rfl⟩ := hs b hb
    exact Finset.mem_image.mpr ⟨a, (mem_pullbackBlock f s a).mpr hb, rfl⟩

/-- Range-contained blocks keep their cardinality under restriction. -/
theorem card_pullbackBlock (f : Fin m ↪o Fin n) (s : Finset (Fin n))
    (hs : ∀ b ∈ s, b ∈ Set.range f) : (pullbackBlock f s).card = s.card := by
  classical
  calc
    (pullbackBlock f s).card = ((pullbackBlock f s).image f).card :=
      (Finset.card_image_of_injective _ f.injective).symm
    _ = s.card := congrArg Finset.card (image_pullbackBlock f s hs)

/-- Inside a coarser block, the restriction of a refinement has exactly the finer
blocks contained in that block. -/
theorem blocks_restrict_of_le {p q : NoncrossingPartition n} (hpq : p ≤ q)
    {s : Finset (Fin n)} (hs : s ∈ q.blocks) :
    (p.restrict (s.orderEmbOfFin rfl)).blocks =
      (p.blocks.filter (fun t => t ⊆ s)).image (pullbackBlock (s.orderEmbOfFin rfl)) := by
  classical
  rw [blocks_restrict]
  congr 1
  apply Finset.filter_congr
  intro t ht
  constructor
  · rintro ⟨a, ha⟩ b hb
    have hfa : s.orderEmbOfFin rfl a ∈ t := (mem_pullbackBlock _ t a).mp ha
    have hrel := hpq ((p.rel_iff_mem_block ht hfa b).mpr hb)
    exact (q.rel_iff_mem_block hs (s.orderEmbOfFin_mem rfl a) b).mp hrel
  · intro hts
    obtain ⟨b, hb⟩ := p.block_nonempty ht
    have hr : b ∈ Set.range (s.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact hts hb
    obtain ⟨a, rfl⟩ := hr
    exact ⟨a, (mem_pullbackBlock _ t a).mpr hb⟩

end FreeProbability.NoncrossingPartition

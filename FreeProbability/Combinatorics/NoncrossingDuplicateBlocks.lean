import FreeProbability.Combinatorics.NoncrossingAdjacent
import FreeProbability.Combinatorics.NoncrossingRestriction
import FreeProbability.Combinatorics.OrderedAdjacentWord

/-!
# Blocks of a partition with a duplicated position

Each block is transported along the order embedding skipping the first duplicate.
The block containing the selected position receives exactly one extra position;
all other blocks keep their cardinality.
-/

namespace FreeProbability.NoncrossingPartition

variable {n : ℕ}

/-- The original block with the duplicated position added precisely when needed. -/
noncomputable def duplicateBlock (i : Fin n) (s : Finset (Fin n)) : Finset (Fin (n + 1)) :=
  if i ∈ s then insert i.castSucc (s.image i.castSucc.succAbove)
    else s.image i.castSucc.succAbove

@[simp] theorem mem_duplicateBlock (i : Fin n) (s : Finset (Fin n)) (a : Fin (n + 1)) :
    a ∈ duplicateBlock i s ↔ i.predAbove a ∈ s := by
  classical
  refine Fin.succAboveCases i.castSucc ?_ (fun a => ?_) a
  · have hnot : i.castSucc ∉ s.image i.castSucc.succAbove := by
      intro h
      obtain ⟨a, _, he⟩ := Finset.mem_image.mp h
      exact i.castSucc.succAbove_ne a he
    by_cases hi : i ∈ s <;> simp [duplicateBlock, hi, hnot]
  · simp only [Fin.predAbove_succAbove]
    have hne := i.castSucc.succAbove_ne a
    have him : i.castSucc.succAbove a ∈ s.image i.castSucc.succAbove ↔ a ∈ s := by
      constructor
      · intro h
        obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp h
        exact i.castSucc.succAbove_right_injective hba ▸ hb
      · intro h
        exact Finset.mem_image.mpr ⟨a, h, rfl⟩
    by_cases hi : i ∈ s <;> simp [duplicateBlock, hi, hne, him]

/-- Pullback along the remaining-position embedding recovers the original block. -/
@[simp] theorem pullback_duplicateBlock (i : Fin n) (s : Finset (Fin n)) :
    pullbackBlock i.castSucc.succAboveOrderEmb (duplicateBlock i s) = s := by
  classical
  ext a
  simp only [mem_pullbackBlock, mem_duplicateBlock]
  change i.predAbove (i.castSucc.succAbove a) ∈ s ↔ a ∈ s
  rw [Fin.predAbove_succAbove]

theorem duplicateBlock_injective (i : Fin n) : Function.Injective (duplicateBlock i) := by
  intro s t h
  have he := congrArg (pullbackBlock i.castSucc.succAboveOrderEmb) h
  simpa only [pullback_duplicateBlock] using he

/-- Exact block-size change under duplication. -/
theorem card_duplicateBlock (i : Fin n) (s : Finset (Fin n)) :
    (duplicateBlock i s).card = s.card + if i ∈ s then 1 else 0 := by
  classical
  have hnot : i.castSucc ∉ s.image i.castSucc.succAbove := by
    intro h
    obtain ⟨a, _, he⟩ := Finset.mem_image.mp h
    exact i.castSucc.succAbove_ne a he
  by_cases hi : i ∈ s <;> simp [duplicateBlock, hi, hnot,
    Finset.card_image_of_injective _ i.castSucc.succAbove_right_injective]

/-- Every block transports to an actual block in the duplicated partition. -/
theorem duplicateBlock_mem_blocks (p : NoncrossingPartition n) (i : Fin n)
    {s : Finset (Fin n)} (hs : s ∈ p.blocks) : duplicateBlock i s ∈ (p.duplicate i).blocks := by
  classical
  obtain ⟨a, ha⟩ := p.block_nonempty hs
  obtain ⟨t, ⟨ht, hat⟩, _⟩ := (p.duplicate i).existsUnique_block (i.castSucc.succAbove a)
  have he : t = duplicateBlock i s := by
    ext b
    rw [← (p.duplicate i).rel_iff_mem_block ht hat b, duplicate_rel,
      Fin.predAbove_succAbove, p.rel_iff_mem_block hs ha (i.predAbove b), mem_duplicateBlock]
  exact he ▸ ht

/-- The entire actual block family is transported by the injective duplication map. -/
theorem blocks_duplicate (p : NoncrossingPartition n) (i : Fin n) :
    (p.duplicate i).blocks = p.blocks.image (duplicateBlock i) := by
  classical
  ext t
  rw [Finset.mem_image]
  constructor
  · intro ht
    obtain ⟨a, hat⟩ := (p.duplicate i).block_nonempty ht
    obtain ⟨s, ⟨hs, has⟩, _⟩ := p.existsUnique_block (i.predAbove a)
    have hai : a ∈ duplicateBlock i s := (mem_duplicateBlock i s a).mpr has
    have he : duplicateBlock i s = t := ((p.duplicate i).existsUnique_block a).unique
      ⟨p.duplicateBlock_mem_blocks i hs, hai⟩ ⟨ht, hat⟩
    exact ⟨s, hs, he⟩
  · rintro ⟨s, hs, rfl⟩
    exact p.duplicateBlock_mem_blocks i hs

/-- Duplication of a block in a proper partition is still shorter than the enlarged word. -/
theorem duplicateBlock_card_lt_of_proper (p : NoncrossingPartition n) (i : Fin n)
    (hp : p ≠ indiscrete n) {s : Finset (Fin n)} (hs : s ∈ p.blocks) :
    (duplicateBlock i s).card < n + 1 := by
  have hlt := p.block_card_lt_of_ne_indiscrete hp hs
  rw [card_duplicateBlock]
  split_ifs <;> omega

/-- Blocks outside the multiplied coordinate have unchanged ordered letters. -/
theorem orderedBlockWord_duplicateBlock_of_not_mem {A : Type*} [Monoid A]
    (x : Fin (n + 1) → A) (i : Fin n) (s : Finset (Fin n)) (hi : i ∉ s) :
    orderedBlockWord x (duplicateBlock i s) = orderedBlockWord (fuseAdjacent x i) s := by
  classical
  simp only [duplicateBlock, hi, ite_false]
  change orderedBlockWord x (s.image i.castSucc.succAboveOrderEmb) = _
  rw [orderedBlockWord_image]
  unfold orderedBlockWord
  apply List.map_congr_left
  intro a ha
  have hai : a ≠ i := by
    intro he
    exact hi (he ▸ (Finset.mem_sort (· ≤ ·)).mp ha)
  simp [fuseAdjacent, hai]

end FreeProbability.NoncrossingPartition

import FreeProbability.Combinatorics.NoncrossingKrewerasSingleton
import FreeProbability.Combinatorics.NoncrossingDuplicateBlocks
import FreeProbability.Combinatorics.NoncrossingReduction

/-!
# Kreweras complementary block count

Deletion reduces an adjacent original chord to a complementary singleton, or a
noninitial original singleton to an adjacent complementary pair. The reduction
lemma avoids cyclic boundary transport. The count is stated only for nonempty
words: at length zero both block families are empty.
-/

namespace FreeProbability.NoncrossingPartition

variable {n : ℕ}

theorem card_blocks_duplicate (p : NoncrossingPartition n) (i : Fin n) :
    (p.duplicate i).blocks.card = p.blocks.card := by
  classical
  rw [p.blocks_duplicate, Finset.card_image_of_injective _ (duplicateBlock_injective i)]

theorem card_blocks_insertSingleton (p : NoncrossingPartition n) (i : Fin (n + 1)) :
    (p.insertSingleton i).blocks.card = p.blocks.card + 1 := by
  classical
  rw [p.blocks_insertSingleton]
  have hn : {i} ∉ p.blocks.image (fun s => s.image i.succAbove) := by
    intro h
    obtain ⟨s, _, he⟩ := Finset.mem_image.mp h
    have hi : i ∈ s.image i.succAbove := he.symm ▸ Finset.mem_singleton_self i
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hi
    exact i.succAbove_ne a ha
  rw [Finset.card_insert_of_notMem hn, Finset.card_image_of_injective _
    (Finset.image_injective i.succAbove_right_injective)]

private theorem card_blocks_one (p : NoncrossingPartition 1) : p.blocks.card = 1 := by
  have hp : p = indiscrete 1 := by
    apply Subtype.ext
    apply Setoid.ext
    intro a b
    constructor
    · intro _
      trivial
    · intro _
      have he : a = b := Subsingleton.elim _ _
      subst b
      exact p.val.refl a
  rw [hp, blocks_indiscrete_of_pos (by omega : 0 < 1)]
  exact Finset.card_singleton _

/-- A nonempty noncrossing partition and its actual right Kreweras complement
have exactly `n + 1` blocks in total. -/
theorem card_blocks_add_kreweras (p : NoncrossingPartition n) (hn : 0 < n) :
    p.blocks.card + p.kreweras.blocks.card = n + 1 := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      rw [card_blocks_one p, card_blocks_one p.kreweras]
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    rcases p.exists_adjacent_or_singleton_succ hnpos with ⟨i, hi⟩ | ⟨i, hi⟩
    · have hcount := ih (p.erase i.castSucc) hnpos
      have hp : p.blocks.card = (p.erase i.castSucc).blocks.card := by
        rw [← p.duplicate_erase i hi]
        simp only [card_blocks_duplicate, erase_duplicate]
      have hk : p.kreweras.blocks.card = (p.erase i.castSucc).kreweras.blocks.card + 1 := by
        rw [p.kreweras_of_adjacent i hi, card_blocks_insertSingleton]
      omega
    · have hcount := ih (p.erase i.succ) hnpos
      have hp : p.blocks.card = (p.erase i.succ).blocks.card + 1 := by
        rw [← p.insertSingleton_erase i.succ hi, card_blocks_insertSingleton, erase_insertSingleton]
      have hk : p.kreweras.blocks.card = (p.erase i.succ).kreweras.blocks.card := by
        rw [p.kreweras_of_singleton_succ i hi, card_blocks_duplicate]
      omega

end FreeProbability.NoncrossingPartition

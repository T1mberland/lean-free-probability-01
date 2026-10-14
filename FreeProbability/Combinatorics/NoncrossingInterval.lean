import FreeProbability.Combinatorics.NoncrossingPartition
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Fin

/-!
# Interval blocks of noncrossing partitions

Every nonempty noncrossing partition has an interval block. Choose the block
with the largest least element. Any gap in this block would contain a block
with a larger least element, by the noncrossing property.
-/

namespace FreeProbability.NoncrossingPartition

variable {n : ℕ}

/-- Every equivalence class has a least representative. -/
theorem exists_least_representative (p : NoncrossingPartition n) (b : Fin n) :
    ∃ i, p.val.r i b ∧ ∀ j, p.val.r i j → i ≤ j := by
  classical
  obtain ⟨s, ⟨hs, hbs⟩, _⟩ := p.existsUnique_block b
  let i := s.min' (p.block_nonempty hs)
  have his : i ∈ s := Finset.min'_mem _ _
  refine ⟨i, (p.same_block_iff i b).mp ⟨s, hs, his, hbs⟩, ?_⟩
  intro j hij
  obtain ⟨t, ht, hit, hjt⟩ := (p.same_block_iff i j).mpr hij
  have hts : t = s := (p.existsUnique_block i).unique ⟨ht, hit⟩ ⟨hs, his⟩
  exact Finset.min'_le _ _ (hts ▸ hjt)

/-- Every nonempty noncrossing partition contains an order-convex block.
No restriction on the sizes of the other blocks is required. -/
theorem exists_interval_block (p : NoncrossingPartition n) (hn : 0 < n) :
    ∃ s ∈ p.blocks, ∀ a ∈ s, ∀ c ∈ s, ∀ b : Fin n,
      a ≤ b → b ≤ c → b ∈ s := by
  classical
  let reps : Finset (Fin n) := Finset.univ.filter
    (fun i => ∀ j, p.val.r i j → i ≤ j)
  have hreps : reps.Nonempty := by
    obtain ⟨i, _, hi⟩ := p.exists_least_representative ⟨0, hn⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  let i := reps.max' hreps
  have hi : ∀ j, p.val.r i j → i ≤ j :=
    (Finset.mem_filter.mp (Finset.max'_mem reps hreps)).2
  obtain ⟨s, ⟨hs, his⟩, _⟩ := p.existsUnique_block i
  refine ⟨s, hs, ?_⟩
  intro a has c hcs b hab hbc
  by_cases hba : b = a
  · exact hba ▸ has
  by_cases hcb : b = c
  · exact hcb ▸ hcs
  have hic : p.val.r i c := (p.same_block_iff i c).mp ⟨s, hs, his, hcs⟩
  have hia : p.val.r i a := (p.same_block_iff i a).mp ⟨s, hs, his, has⟩
  have hib : i < b := lt_of_le_of_lt (hi a hia) (lt_of_le_of_ne hab (Ne.symm hba))
  have hbc' : b < c := lt_of_le_of_ne hbc hcb
  obtain ⟨j, hjb, hj⟩ := p.exists_least_representative b
  have hji : j ≤ i := Finset.le_max' reps j (Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hj⟩)
  have hir : p.val.r i b := by
    rcases eq_or_lt_of_le hji with he | hlt
    · exact he ▸ hjb
    · have hrel : p.val.r j i := p.property j i b c hlt hib hbc' hjb hic
      exact p.val.trans (p.val.symm hrel) hjb
  obtain ⟨t, ht, hit, hbt⟩ := (p.same_block_iff i b).mpr hir
  have hts : t = s := (p.existsUnique_block i).unique ⟨ht, hit⟩ ⟨hs, his⟩
  exact hts ▸ hbt

/-- An interval block can be represented by its inclusive endpoints. -/
theorem exists_Icc_block (p : NoncrossingPartition n) (hn : 0 < n) :
    ∃ a b : Fin n, a ≤ b ∧ Finset.Icc a b ∈ p.blocks := by
  classical
  obtain ⟨s, hs, hconv⟩ := p.exists_interval_block hn
  have hne := p.block_nonempty hs
  let a := s.min' hne
  let b := s.max' hne
  have ha : a ∈ s := Finset.min'_mem _ _
  have hb : b ∈ s := Finset.max'_mem _ _
  have hsI : s = Finset.Icc a b := by
    ext j
    constructor
    · intro hj
      exact Finset.mem_Icc.mpr ⟨Finset.min'_le _ _ hj, Finset.le_max' _ _ hj⟩
    · intro hj
      obtain ⟨haj, hjb⟩ := Finset.mem_Icc.mp hj
      exact hconv a ha b hb j haj hjb
  exact ⟨a, b, Finset.min'_le _ _ hb, hsI ▸ hs⟩

end FreeProbability.NoncrossingPartition

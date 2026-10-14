import FreeProbability.Combinatorics.NoncrossingPartition
import Lean.Elab.Tactic.Omega

/-!
# Singleton blocks in noncrossing partitions

If no two adjacent positions belong to one block, a nonempty noncrossing
partition has a singleton block. A shortest related pair encloses a singleton.
This is the combinatorial input for centered alternating cumulant expansions.
-/

namespace FreeProbability.NoncrossingPartition

variable {n : ℕ}

/-- A singleton equivalence class is an actual singleton block. -/
theorem singleton_mem_blocks (p : NoncrossingPartition n) (i : Fin n)
    (hi : ∀ j, p.val.r i j → j = i) : {i} ∈ p.blocks := by
  obtain ⟨s, ⟨hs, his⟩, _⟩ := p.existsUnique_block i
  have he : s = {i} := by
    ext j
    constructor
    · intro hjs
      have hrel := (p.same_block_iff i j).mp ⟨s, hs, his, hjs⟩
      exact Finset.mem_singleton.mpr (hi j hrel)
    · intro hji
      exact (Finset.mem_singleton.mp hji).symm ▸ his
  exact he ▸ hs

/-- A nonempty noncrossing partition without any adjacent related positions has
a singleton equivalence class. -/
theorem exists_singleton_of_no_adjacent (p : NoncrossingPartition n) (hn : 0 < n)
    (hsep : ∀ i j : Fin n, i.val + 1 = j.val → ¬p.val.r i j) :
    ∃ i : Fin n, ∀ j : Fin n, p.val.r i j → j = i := by
  classical
  by_cases hex : ∃ i j : Fin n, i < j ∧ p.val.r i j
  · let P : ℕ → Prop := fun d => ∃ i j : Fin n, i < j ∧ p.val.r i j ∧ j.val - i.val = d
    have hexP : ∃ d, P d := by
      obtain ⟨i, j, hij, hr⟩ := hex
      exact ⟨_, i, j, hij, hr, rfl⟩
    obtain ⟨i, j, hij, hr, hdist⟩ := Nat.find_spec hexP
    have hmin (a b : Fin n) (hab : a < b) (hrab : p.val.r a b) :
        Nat.find hexP ≤ b.val - a.val := Nat.find_min' hexP ⟨a, b, hab, hrab, rfl⟩
    have hgap : i.val + 1 < j.val := by
      have hnot : i.val + 1 ≠ j.val := fun he => hsep i j he hr
      have hlt : i.val < j.val := hij
      omega
    let k : Fin n := ⟨i.val + 1, lt_trans hgap j.isLt⟩
    have hik : i < k := by change i.val < i.val + 1; omega
    have hkj : k < j := hgap
    have hnik : ¬p.val.r i k := hsep i k rfl
    refine ⟨k, ?_⟩
    intro l hkl
    rcases lt_trichotomy l k with hlk | rfl | hklgt
    · by_cases hli : l = i
      · subst l
        exact False.elim (hnik (p.val.symm hkl))
      · have hli : l < i := by
          have hneq : l.val ≠ i.val := fun he => hli (Fin.ext he)
          change l.val < k.val at hlk
          change l.val < i.val
          dsimp [k] at hlk
          omega
        have hrel : p.val.r l i := p.property l i k j hli hik hkj (p.val.symm hkl) hr
        exact False.elim (hnik (p.val.trans (p.val.symm hrel) (p.val.symm hkl)))
    · rfl
    · rcases lt_trichotomy l j with hlj | rfl | hjl
      · have hbound := hmin k l hklgt hkl
        have hklv : k.val < l.val := hklgt
        have hljv : l.val < j.val := hlj
        dsimp [k] at hbound hklv
        omega
      · exact False.elim (hnik (p.val.trans hr (p.val.symm hkl)))
      · exact False.elim (hnik (p.property i k j l hik hkj hjl hr hkl))
  · refine ⟨⟨0, hn⟩, ?_⟩
    intro j hr
    rcases lt_trichotomy j ⟨0, hn⟩ with hlt | heq | hgt
    · exact False.elim (hex ⟨j, _, hlt, p.val.symm hr⟩)
    · exact heq
    · exact False.elim (hex ⟨_, j, hgt, hr⟩)

/-- If each block is monochromatic for an adjacent-alternating coloring, then
the partition has a singleton. -/
theorem exists_singleton_of_alternating_coloring {I : Type*}
    (p : NoncrossingPartition n) (hn : 0 < n) (color : Fin n → I)
    (halt : ∀ i j : Fin n, i.val + 1 = j.val → color i ≠ color j)
    (hmono : ∀ i j, p.val.r i j → color i = color j) :
    ∃ i : Fin n, ∀ j : Fin n, p.val.r i j → j = i :=
  p.exists_singleton_of_no_adjacent hn (fun i j hij hr => halt i j hij (hmono i j hr))

end FreeProbability.NoncrossingPartition

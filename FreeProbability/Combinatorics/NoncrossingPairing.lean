import FreeProbability.Combinatorics.NoncrossingSingleton
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Parity

/-!
# Noncrossing pairings

A noncrossing pairing is a noncrossing partition whose actual blocks all have
size two. Each position has a unique distinct partner; pairing partners form a
fixed-point-free involution. Every nonempty pairing has an adjacent pair, the
first combinatorial input for the free Wick recursion.
-/

namespace FreeProbability

/-- A pairing condition on the actual equivalence classes. -/
def NoncrossingPartition.IsPairing {n : ℕ} (p : NoncrossingPartition n) : Prop :=
  ∀ s ∈ p.blocks, s.card = 2

/-- Noncrossing partitions consisting entirely of two-element blocks. -/
abbrev NoncrossingPairing (n : ℕ) := {p : NoncrossingPartition n // p.IsPairing}

namespace NoncrossingPartition

variable {n : ℕ} {p : NoncrossingPartition n}

/-- The number of positions is twice the number of pairs. -/
theorem IsPairing.card_eq_twice (hp : p.IsPairing) : n = 2 * p.blocks.card := by
  classical
  calc
    n = ∑ s ∈ p.blocks, s.card := p.sum_block_sizes.symm
    _ = ∑ _s ∈ p.blocks, 2 :=
      Finset.sum_congr rfl (fun s hs => hp s hs)
    _ = 2 * p.blocks.card := by simp [Nat.mul_comm]

/-- Noncrossing pairings have even size. -/
theorem IsPairing.even (hp : p.IsPairing) : Even n := by
  refine ⟨p.blocks.card, ?_⟩
  exact hp.card_eq_twice.trans (by omega)

/-- Every position in a pairing has exactly one distinct related position. -/
theorem IsPairing.existsUnique_partner (hp : p.IsPairing) (i : Fin n) :
    ∃! j, j ≠ i ∧ p.val.r i j := by
  classical
  obtain ⟨s, ⟨hs, his⟩, _⟩ := p.existsUnique_block i
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp (hp s hs)
  have hi : i = a ∨ i = b := by simpa using his
  rcases hi with hi | hi
  · subst i
    refine ⟨b, ⟨Ne.symm hab, (p.same_block_iff a b).mp
      ⟨{a, b}, hs, by simp, by simp⟩⟩, ?_⟩
    intro j hj
    obtain ⟨t, ht, hat, hjt⟩ := (p.same_block_iff a j).mpr hj.2
    have hts : t = {a, b} :=
      (p.existsUnique_block a).unique ⟨ht, hat⟩ ⟨hs, by simp⟩
    have : j = a ∨ j = b := by simpa [hts] using hjt
    exact this.resolve_left hj.1
  · subst i
    refine ⟨a, ⟨hab, (p.same_block_iff b a).mp
      ⟨{a, b}, hs, by simp, by simp⟩⟩, ?_⟩
    intro j hj
    obtain ⟨t, ht, hbt, hjt⟩ := (p.same_block_iff b j).mpr hj.2
    have hts : t = {a, b} :=
      (p.existsUnique_block b).unique ⟨ht, hbt⟩ ⟨hs, by simp⟩
    have : j = a ∨ j = b := by simpa [hts] using hjt
    exact this.resolve_right hj.1

/-- Every nonempty noncrossing pairing has a pair of consecutive positions. -/
theorem IsPairing.exists_adjacent (hp : p.IsPairing) (hn : 0 < n) :
    ∃ i j : Fin n, i.val + 1 = j.val ∧ p.val.r i j := by
  classical
  by_contra h
  have hsep : ∀ i j : Fin n, i.val + 1 = j.val → ¬p.val.r i j := by
    intro i j hij hr
    exact h ⟨i, j, hij, hr⟩
  obtain ⟨i, hi⟩ := p.exists_singleton_of_no_adjacent hn hsep
  obtain ⟨j, hj, _⟩ := hp.existsUnique_partner i
  exact hj.1 (hi j hj.2)

end NoncrossingPartition

namespace NoncrossingPairing

variable {n : ℕ}

noncomputable instance : Fintype (NoncrossingPairing n) := Fintype.ofFinite _

/-- The unique distinct position in the same block. -/
noncomputable def partner (p : NoncrossingPairing n) (i : Fin n) : Fin n :=
  Classical.choose (p.property.existsUnique_partner i)

theorem partner_ne (p : NoncrossingPairing n) (i : Fin n) : p.partner i ≠ i :=
  (Classical.choose_spec (p.property.existsUnique_partner i)).1.1

theorem rel_partner (p : NoncrossingPairing n) (i : Fin n) : p.val.val.r i (p.partner i) :=
  (Classical.choose_spec (p.property.existsUnique_partner i)).1.2

@[simp] theorem partner_partner (p : NoncrossingPairing n) (i : Fin n) :
    p.partner (p.partner i) = i := by
  apply ((Classical.choose_spec (p.property.existsUnique_partner (p.partner i))).2
    i ⟨Ne.symm (p.partner_ne i), p.val.val.symm (p.rel_partner i)⟩).symm

/-- The pairing relation is exactly equality or partnership. -/
theorem rel_iff (p : NoncrossingPairing n) (i j : Fin n) :
    p.val.val.r i j ↔ j = i ∨ j = p.partner i := by
  constructor
  · intro h
    by_cases hji : j = i
    · exact Or.inl hji
    · exact Or.inr ((Classical.choose_spec (p.property.existsUnique_partner i)).2 j ⟨hji, h⟩)
  · intro h
    rcases h with h | h
    · simpa [h] using p.val.val.refl i
    · simpa [h] using p.rel_partner i

/-- Odd-sized noncrossing pairings do not exist. -/
theorem not_nonempty_of_odd (hn : Odd n) : ¬Nonempty (NoncrossingPairing n) := by
  rintro ⟨p⟩
  exact (Nat.not_even_iff_odd.mpr hn) p.property.even

end NoncrossingPairing
end FreeProbability

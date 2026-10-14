import FreeProbability.Combinatorics.NoncrossingSingleton
import Mathlib.Order.Fin.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Insertion and deletion of singleton blocks

Deleting a position restricts the partition along its order embedding. Conversely,
one can insert a new singleton at any position without introducing crossings.
The two operations give an equivalence between noncrossing partitions of `n`
and those of `n + 1` with a prescribed singleton position.
-/

namespace FreeProbability.NoncrossingPartition

variable {n : ℕ}

/-- Delete a position and renumber the remaining positions in increasing order. -/
def erase (p : NoncrossingPartition (n + 1)) (i : Fin (n + 1)) :
    NoncrossingPartition n :=
  ⟨Setoid.comap i.succAbove p.val, p.property.comap i.succAboveOrderEmb⟩

private def optionSetoid (p : Setoid (Fin n)) : Setoid (Option (Fin n)) where
  r a b := match a, b with
    | none, none => True
    | some a, some b => p.r a b
    | _, _ => False
  iseqv := {
    refl := by intro a; cases a with
      | none => trivial
      | some a => exact p.refl a
    symm := by intro a b; cases a <;> cases b <;> simp_all; exact p.symm
    trans := by intro a b c; cases a <;> cases b <;> cases c <;> simp_all; exact p.trans }

private def insertedSetoid (p : NoncrossingPartition n) (i : Fin (n + 1)) :
    Setoid (Fin (n + 1)) := Setoid.comap (finSuccEquiv' i) (optionSetoid p.val)

private theorem inserted_related_of_ne (p : NoncrossingPartition n) (i : Fin (n + 1))
    {a b : Fin (n + 1)} (hne : a ≠ b) (h : (insertedSetoid p i).r a b) :
    ∃ x y : Fin n, a = i.succAbove x ∧ b = i.succAbove y ∧ p.val.r x y := by
  change (optionSetoid p.val).r (finSuccEquiv' i a) (finSuccEquiv' i b) at h
  cases ha : finSuccEquiv' i a with
  | none =>
    cases hb : finSuccEquiv' i b with
    | none =>
      exact False.elim (hne ((finSuccEquiv'_eq_none.mp ha).symm.trans
        (finSuccEquiv'_eq_none.mp hb)))
    | some y =>
      rw [ha, hb] at h
      exact False.elim h
  | some x =>
    cases hb : finSuccEquiv' i b with
    | none =>
      rw [ha, hb] at h
      exact False.elim h
    | some y =>
      rw [ha, hb] at h
      exact ⟨x, y, finSuccEquiv'_eq_some.mp ha, finSuccEquiv'_eq_some.mp hb,
        h⟩

private theorem inserted_nonCrossing (p : NoncrossingPartition n) (i : Fin (n + 1)) :
    IsNoncrossing (insertedSetoid p i) := by
  intro a b c d hab hbc hcd hac hbd
  obtain ⟨x, z, rfl, rfl, hxz⟩ := inserted_related_of_ne p i (ne_of_lt (lt_trans hab hbc)) hac
  obtain ⟨y, w, rfl, rfl, hyw⟩ := inserted_related_of_ne p i (ne_of_lt (lt_trans hbc hcd)) hbd
  have hxy : x < y := i.succAboveOrderEmb.lt_iff_lt.mp hab
  have hyz : y < z := i.succAboveOrderEmb.lt_iff_lt.mp hbc
  have hzw : z < w := i.succAboveOrderEmb.lt_iff_lt.mp hcd
  change (optionSetoid p.val).r (finSuccEquiv' i (i.succAbove x))
    (finSuccEquiv' i (i.succAbove y))
  rw [finSuccEquiv'_succAbove, finSuccEquiv'_succAbove]
  exact p.property x y z w hxy hyz hzw hxz hyw

/-- Insert a new singleton at the given position. -/
def insertSingleton (p : NoncrossingPartition n) (i : Fin (n + 1)) :
    NoncrossingPartition (n + 1) := ⟨insertedSetoid p i, inserted_nonCrossing p i⟩

@[simp] theorem insertSingleton_rel_succAbove (p : NoncrossingPartition n)
    (i : Fin (n + 1)) (a b : Fin n) :
    (p.insertSingleton i).val.r (i.succAbove a) (i.succAbove b) ↔ p.val.r a b := by
  change (optionSetoid p.val).r (finSuccEquiv' i (i.succAbove a))
    (finSuccEquiv' i (i.succAbove b)) ↔ _
  rw [finSuccEquiv'_succAbove, finSuccEquiv'_succAbove]
  rfl

@[simp] theorem insertSingleton_rel_at (p : NoncrossingPartition n)
    (i j : Fin (n + 1)) : (p.insertSingleton i).val.r i j ↔ j = i := by
  change (optionSetoid p.val).r (finSuccEquiv' i i) (finSuccEquiv' i j) ↔ _
  rw [finSuccEquiv'_at]
  cases hj : finSuccEquiv' i j with
  | none =>
    change True ↔ j = i
    simp [(finSuccEquiv'_eq_none.mp hj).symm]
  | some a =>
    have hji : j ≠ i := by
      intro hji
      subst j
      simp at hj
    change False ↔ j = i
    simp [hji]

@[simp] theorem erase_insertSingleton (p : NoncrossingPartition n) (i : Fin (n + 1)) :
    (p.insertSingleton i).erase i = p := by
  apply Subtype.ext
  exact Setoid.ext (fun a b => p.insertSingleton_rel_succAbove i a b)

/-- Reinserting a deleted singleton recovers the entire partition. -/
theorem insertSingleton_erase (p : NoncrossingPartition (n + 1)) (i : Fin (n + 1))
    (hi : ∀ j, p.val.r i j → j = i) : (p.erase i).insertSingleton i = p := by
  apply Subtype.ext
  apply Setoid.ext
  rw [Fin.forall_iff_succAbove i]
  constructor
  · intro b
    rw [insertSingleton_rel_at]
    exact ⟨fun h => h ▸ p.val.refl i, hi b⟩
  · intro a
    rw [Fin.forall_iff_succAbove i]
    constructor
    · constructor
      · intro h
        have he : i.succAbove a = i :=
          ((p.erase i).insertSingleton_rel_at i (i.succAbove a)).mp (((p.erase i).insertSingleton i).val.symm h)
        exact False.elim (i.succAbove_ne a he)
      · intro h
        exact False.elim (i.succAbove_ne a (hi _ (p.val.symm h)))
    · intro b
      exact (p.erase i).insertSingleton_rel_succAbove i a b

/-- Singleton insertion is a bijection onto partitions with the specified singleton. -/
def singletonInsertionEquiv (i : Fin (n + 1)) : NoncrossingPartition n ≃
    {p : NoncrossingPartition (n + 1) // ∀ j, p.val.r i j → j = i} where
  toFun p := ⟨p.insertSingleton i, fun j h => (p.insertSingleton_rel_at i j).mp h⟩
  invFun p := p.val.erase i
  left_inv p := p.erase_insertSingleton i
  right_inv p := Subtype.ext (p.val.insertSingleton_erase i p.property)

/-- Membership in a specified block is exactly relation to any of its positions. -/
theorem rel_iff_mem_block (p : NoncrossingPartition n) {s : Finset (Fin n)}
    (hs : s ∈ p.blocks) {a : Fin n} (ha : a ∈ s) (b : Fin n) :
    p.val.r a b ↔ b ∈ s := by
  constructor
  · intro h
    obtain ⟨t, ht, hat, hbt⟩ := (p.same_block_iff a b).mpr h
    have hts : t = s := (p.existsUnique_block a).unique ⟨ht, hat⟩ ⟨hs, ha⟩
    exact hts ▸ hbt
  · intro hb
    exact (p.same_block_iff a b).mp ⟨s, hs, ha, hb⟩

/-- The new position is an actual singleton block. -/
theorem singleton_mem_blocks_insertSingleton (p : NoncrossingPartition n)
    (i : Fin (n + 1)) : {i} ∈ (p.insertSingleton i).blocks :=
  (p.insertSingleton i).singleton_mem_blocks i
    (fun j h => (p.insertSingleton_rel_at i j).mp h)

/-- Every old block becomes its order-preserving image after singleton insertion. -/
theorem image_mem_blocks_insertSingleton (p : NoncrossingPartition n)
    (i : Fin (n + 1)) {s : Finset (Fin n)} (hs : s ∈ p.blocks) :
    s.image i.succAbove ∈ (p.insertSingleton i).blocks := by
  classical
  obtain ⟨a, ha⟩ := p.block_nonempty hs
  obtain ⟨t, ⟨ht, hat⟩, _⟩ := (p.insertSingleton i).existsUnique_block (i.succAbove a)
  have he : t = s.image i.succAbove := by
    ext b
    refine Fin.succAboveCases i ?_ (fun b => ?_) b
    · have hti : i ∉ t := by
        intro hit
        have hrel := ((p.insertSingleton i).rel_iff_mem_block ht hat i).mpr hit
        exact i.succAbove_ne a ((p.insertSingleton_rel_at i (i.succAbove a)).mp
          ((p.insertSingleton i).val.symm hrel))
      have hii : i ∉ s.image i.succAbove := by
        intro h
        obtain ⟨b, _, hb⟩ := Finset.mem_image.mp h
        exact i.succAbove_ne b hb
      simp [hti, hii]
    · rw [← (p.insertSingleton i).rel_iff_mem_block ht hat (i.succAbove b),
        p.insertSingleton_rel_succAbove i a b, p.rel_iff_mem_block hs ha b]
      constructor
      · intro hb
        exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
      · intro hb
        obtain ⟨c, hc, hcb⟩ := Finset.mem_image.mp hb
        exact i.succAbove_right_injective hcb ▸ hc
  exact he ▸ ht

/-- Insertion adds exactly one singleton block and transports all existing blocks. -/
theorem blocks_insertSingleton (p : NoncrossingPartition n) (i : Fin (n + 1)) :
    (p.insertSingleton i).blocks =
      insert {i} (p.blocks.image (fun s => s.image i.succAbove)) := by
  classical
  ext t
  rw [Finset.mem_insert, Finset.mem_image]
  constructor
  · intro ht
    obtain ⟨b, hbt⟩ := (p.insertSingleton i).block_nonempty ht
    cases hb : finSuccEquiv' i b with
    | none =>
      have hbi : b = i := (finSuccEquiv'_eq_none.mp hb).symm
      exact Or.inl (((p.insertSingleton i).existsUnique_block i).unique
        ⟨ht, hbi ▸ hbt⟩ ⟨p.singleton_mem_blocks_insertSingleton i, by simp⟩)
    | some a =>
      have hba : b = i.succAbove a := finSuccEquiv'_eq_some.mp hb
      obtain ⟨s, ⟨hs, has⟩, _⟩ := p.existsUnique_block a
      have hi : i.succAbove a ∈ s.image i.succAbove :=
        Finset.mem_image.mpr ⟨a, has, rfl⟩
      have he : s.image i.succAbove = t :=
        ((p.insertSingleton i).existsUnique_block (i.succAbove a)).unique
          ⟨p.image_mem_blocks_insertSingleton i hs, hi⟩ ⟨ht, hba ▸ hbt⟩
      exact Or.inr ⟨s, hs, he⟩
  · rintro (rfl | ⟨s, hs, rfl⟩)
    · exact p.singleton_mem_blocks_insertSingleton i
    · exact p.image_mem_blocks_insertSingleton i hs

end FreeProbability.NoncrossingPartition

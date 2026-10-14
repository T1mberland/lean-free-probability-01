import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Partition.Finpartition

/-!
# Noncrossing partitions of an ordered finite set

A partition is an equivalence relation, avoiding choices of block labels. The
noncrossing condition says that interlaced related pairs belong to the same block.
Actual blocks are provided as a finite partition for moment–cumulant sums.
-/

namespace FreeProbability

variable {n : ℕ}

/-- Ordered noncrossing criterion for equivalence relations on `Fin n`. -/
def IsNoncrossing (p : Setoid (Fin n)) : Prop :=
  ∀ a b c d : Fin n, a < b → b < c → c < d → p.r a c → p.r b d → p.r a b

/-- A noncrossing partition, with blocks represented intrinsically by equivalence classes. -/
abbrev NoncrossingPartition (n : ℕ) := {p : Setoid (Fin n) // IsNoncrossing p}

instance finiteSetoidFin : Finite (Setoid (Fin n)) := by
  apply Finite.of_injective (fun p : Setoid (Fin n) => p.r)
  intro p q h
  exact Setoid.ext (fun a b => (congrFun (congrFun h a) b).to_iff)

noncomputable instance : Fintype (NoncrossingPartition n) := Fintype.ofFinite _

theorem isNoncrossing_bot : IsNoncrossing (⊥ : Setoid (Fin n)) := by
  intro a b c d hab hbc hcd hac _
  have he : a = c := hac
  subst c
  exact False.elim ((lt_trans hab hbc).false)

theorem isNoncrossing_top : IsNoncrossing (⊤ : Setoid (Fin n)) := by
  intro _ _ _ _ _ _ _ _ _
  trivial

theorem IsNoncrossing.inf {p q : Setoid (Fin n)} (hp : IsNoncrossing p)
    (hq : IsNoncrossing q) : IsNoncrossing (p ⊓ q) := by
  intro a b c d hab hbc hcd hac hbd
  exact ⟨hp a b c d hab hbc hcd hac.1 hbd.1,
    hq a b c d hab hbc hcd hac.2 hbd.2⟩

/-- Pullback along an order embedding preserves noncrossing. -/
theorem IsNoncrossing.comap {m : ℕ} {p : Setoid (Fin n)} (hp : IsNoncrossing p)
    (f : Fin m ↪o Fin n) : IsNoncrossing (Setoid.comap f p) := by
  intro a b c d hab hbc hcd hac hbd
  exact hp (f a) (f b) (f c) (f d) (f.lt_iff_lt.mpr hab)
    (f.lt_iff_lt.mpr hbc) (f.lt_iff_lt.mpr hcd) hac hbd

namespace NoncrossingPartition

/-- The discrete partition. -/
def discrete (n : ℕ) : NoncrossingPartition n := ⟨⊥, isNoncrossing_bot⟩

/-- The single-block partition (empty when `n = 0`). -/
def indiscrete (n : ℕ) : NoncrossingPartition n := ⟨⊤, isNoncrossing_top⟩

instance : Inhabited (NoncrossingPartition n) := ⟨indiscrete n⟩

/-- The actual finite partition into nonempty equivalence classes. -/
noncomputable def toFinpartition (p : NoncrossingPartition n) :
    Finpartition (Finset.univ : Finset (Fin n)) := by
  classical
  exact Finpartition.ofSetoid p.val

/-- The blocks, represented as finite subsets of the ordered set. -/
noncomputable def blocks (p : NoncrossingPartition n) : Finset (Finset (Fin n)) :=
  p.toFinpartition.parts

theorem block_nonempty (p : NoncrossingPartition n) {s : Finset (Fin n)} (hs : s ∈ p.blocks) :
    s.Nonempty := p.toFinpartition.nonempty_of_mem_parts hs

theorem existsUnique_block (p : NoncrossingPartition n) (i : Fin n) :
    ∃! s, s ∈ p.blocks ∧ i ∈ s := p.toFinpartition.existsUnique_mem (Finset.mem_univ i)

theorem sum_block_sizes (p : NoncrossingPartition n) :
    ∑ s ∈ p.blocks, s.card = n := by
  simpa [blocks] using p.toFinpartition.sum_card_parts

theorem same_block_iff (p : NoncrossingPartition n) (i j : Fin n) :
    (∃ s ∈ p.blocks, i ∈ s ∧ j ∈ s) ↔ p.val.r i j := by
  classical
  have h : (j ∈ p.toFinpartition.part i) ↔ p.val.r i j :=
    Finpartition.mem_part_ofSetoid_iff_rel
  rw [Finpartition.mem_part_iff_exists] at h
  simpa only [blocks, and_comm] using h

@[simp] theorem blocks_zero (p : NoncrossingPartition 0) : p.blocks = ∅ :=
  p.toFinpartition.parts_eq_empty_iff.mpr (by simp)

theorem eq_indiscrete_of_univ_mem (p : NoncrossingPartition n)
    (h : Finset.univ ∈ p.blocks) : p = indiscrete n := by
  apply Subtype.ext
  apply Setoid.ext
  intro i j
  constructor
  · intro _
    trivial
  · intro _
    exact (p.same_block_iff i j).mp ⟨Finset.univ, h, Finset.mem_univ _, Finset.mem_univ _⟩

/-- Every block of a partition other than the one-block partition is strictly
shorter than the full word. This is the termination fact for cumulant recursion. -/
theorem block_card_lt_of_ne_indiscrete (p : NoncrossingPartition n)
    (hp : p ≠ indiscrete n) {s : Finset (Fin n)} (hs : s ∈ p.blocks) : s.card < n := by
  classical
  by_contra hn
  have he : s = Finset.univ := Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    (by simpa using (not_lt.mp hn))
  exact hp (p.eq_indiscrete_of_univ_mem (he ▸ hs))

theorem blocks_indiscrete_of_pos (hn : 0 < n) :
    (indiscrete n).blocks = {Finset.univ} := by
  classical
  let _ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  change (Finset.univ : Finset (Fin n)).image (fun a : Fin n =>
    {b ∈ (Finset.univ : Finset (Fin n)) | (⊤ : Setoid (Fin n)).r a b}) =
      {(Finset.univ : Finset (Fin n))}
  simp
  exact Finset.image_const (Finset.univ_nonempty) _

instance : Subsingleton (NoncrossingPartition 0) := ⟨fun p q => by
  apply Subtype.ext
  exact Setoid.ext (fun i _ => Fin.elim0 i)⟩

instance : Subsingleton (NoncrossingPartition 1) := ⟨fun p q => by
  apply Subtype.ext
  apply Setoid.ext
  intro i j
  have he : i = j := Subsingleton.elim i j
  subst j
  exact ⟨fun _ => q.val.refl i, fun _ => p.val.refl i⟩⟩

@[simp] theorem card_zero : Fintype.card (NoncrossingPartition 0) = 1 := by
  let _ : Unique (NoncrossingPartition 0) :=
    { default := indiscrete 0, uniq := fun _ => Subsingleton.elim _ _ }
  exact Fintype.card_unique

@[simp] theorem card_one : Fintype.card (NoncrossingPartition 1) = 1 := by
  let _ : Unique (NoncrossingPartition 1) :=
    { default := indiscrete 1, uniq := fun _ => Subsingleton.elim _ _ }
  exact Fintype.card_unique

end NoncrossingPartition
end FreeProbability

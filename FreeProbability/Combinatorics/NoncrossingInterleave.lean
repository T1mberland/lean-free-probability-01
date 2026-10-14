import FreeProbability.Combinatorics.NoncrossingKreweras
import FreeProbability.Combinatorics.NoncrossingRestriction

/-! # Restriction and reconstruction of Kreweras-compatible interleavings -/

namespace FreeProbability.NoncrossingPartition

variable {n : ℕ}

/-- Ordered embedding of original positions. -/
def oddOrderEmbedding : Fin n ↪o Fin (2 * n) :=
  OrderEmbedding.ofStrictMono oddPosition (by
    intro a b hab
    change 2 * a.val < 2 * b.val
    have : a.val < b.val := hab
    omega)

/-- Ordered embedding of complementary positions. -/
def evenOrderEmbedding : Fin n ↪o Fin (2 * n) :=
  OrderEmbedding.ofStrictMono evenPosition (by
    intro a b hab
    change 2 * a.val + 1 < 2 * b.val + 1
    have : a.val < b.val := hab
    omega)

@[simp] theorem halfPosition_odd (i : Fin n) : halfPosition (oddPosition i) = i := by
  apply Fin.ext
  change 2 * i.val / 2 = i.val
  omega

/-- The interleaved noncrossing partition associated to any compatible pair. -/
def interleave (p q : NoncrossingPartition n) (hq : q ≤ p.kreweras) :
    NoncrossingPartition (2 * n) :=
  ⟨interleaveSetoid p q, interleave_nonCrossing_of_le_kreweras p q hq⟩

@[simp] theorem restrict_interleave_odd (p q : NoncrossingPartition n) (hq : q ≤ p.kreweras) :
    (p.interleave q hq).restrict oddOrderEmbedding = p := by
  apply Subtype.ext
  apply Setoid.ext
  intro a b
  exact interleave_odd_odd p q a b

@[simp] theorem restrict_interleave_even (p q : NoncrossingPartition n) (hq : q ≤ p.kreweras) :
    (p.interleave q hq).restrict evenOrderEmbedding = q := by
  apply Subtype.ext
  apply Setoid.ext
  intro a b
  exact interleave_even_even p q a b

/-- Every block contains only original positions or only complementary positions. -/
def ParityPreserving (r : NoncrossingPartition (2 * n)) : Prop :=
  ∀ a b, r.val.r a b → a.val % 2 = b.val % 2

theorem interleave_parityPreserving (p q : NoncrossingPartition n) (hq : q ≤ p.kreweras) :
    (p.interleave q hq).ParityPreserving := fun _ _ h => h.1

/-- Every doubled-word position has exactly one parity representation. -/
theorem position_cases (a : Fin (2 * n)) :
    a = oddPosition (halfPosition a) ∨ a = evenPosition (halfPosition a) := by
  by_cases h : a.val % 2 = 0
  · left
    apply Fin.ext
    change a.val = 2 * (a.val / 2)
    omega
  · right
    apply Fin.ext
    change a.val = 2 * (a.val / 2) + 1
    omega

/-- A parity-preserving partition is recovered exactly from its two restrictions. -/
theorem parityPreserving_reconstruction (r : NoncrossingPartition (2 * n))
    (hr : r.ParityPreserving) :
    r.val = interleaveSetoid (r.restrict oddOrderEmbedding) (r.restrict evenOrderEmbedding) := by
  apply Setoid.ext
  intro a b
  rcases position_cases a with ha | ha <;> rcases position_cases b with hb | hb
  · rw [ha, hb, interleave_odd_odd]
    rfl
  · rw [ha, hb]
    constructor
    · intro h
      have hp := hr _ _ h
      change (2 * (halfPosition a).val) % 2 = (2 * (halfPosition b).val + 1) % 2 at hp
      omega
    · intro h
      exact False.elim (interleave_odd_even _ _ _ _ h)
  · rw [ha, hb]
    constructor
    · intro h
      have hp := hr _ _ h
      change (2 * (halfPosition a).val + 1) % 2 = (2 * (halfPosition b).val) % 2 at hp
      omega
    · intro h
      exact False.elim (interleave_odd_even _ _ _ _ ((interleaveSetoid _ _).symm h))
  · rw [ha, hb, interleave_even_even]
    rfl

/-- The complementary restriction lies below the actual Kreweras complement. -/
theorem restrict_even_le_kreweras (r : NoncrossingPartition (2 * n))
    (hr : r.ParityPreserving) :
    r.restrict evenOrderEmbedding ≤ (r.restrict oddOrderEmbedding).kreweras := by
  apply (interleave_nonCrossing_iff _ _).mp
  rw [← r.parityPreserving_reconstruction hr]
  exact r.property

/-- Reconstruction at the noncrossing-partition level. -/
theorem interleave_restrict (r : NoncrossingPartition (2 * n)) (hr : r.ParityPreserving) :
    (r.restrict oddOrderEmbedding).interleave (r.restrict evenOrderEmbedding)
      (r.restrict_even_le_kreweras hr) = r := by
  exact Subtype.ext (r.parityPreserving_reconstruction hr).symm

/-- Noncrossing partitions with blocks confined to one parity. -/
abbrev ParityNoncrossing (n : ℕ) :=
  {r : NoncrossingPartition (2 * n) // r.ParityPreserving}

/-- Original partitions with an arbitrary refinement of their actual complement. -/
abbrev KrewerasCompatiblePairs (n : ℕ) :=
  Σ p : NoncrossingPartition n, {q : NoncrossingPartition n // q ≤ p.kreweras}

/-- Every parity-preserving noncrossing partition corresponds uniquely to one
original partition and one refinement of its Kreweras complement. -/
def parityInterleaveEquiv : ParityNoncrossing n ≃ KrewerasCompatiblePairs n where
  toFun r := ⟨r.val.restrict oddOrderEmbedding,
    ⟨r.val.restrict evenOrderEmbedding, r.val.restrict_even_le_kreweras r.property⟩⟩
  invFun z := ⟨z.1.interleave z.2.val z.2.property,
    z.1.interleave_parityPreserving z.2.val z.2.property⟩
  left_inv r := Subtype.ext (r.val.interleave_restrict r.property)
  right_inv z := by
    rcases z with ⟨p, ⟨q, hq⟩⟩
    apply Sigma.ext (restrict_interleave_odd p q hq)
    apply (Subtype.heq_iff_coe_eq (fun z => by
      change z ≤ ((p.interleave q hq).restrict oddOrderEmbedding).kreweras ↔ z ≤ p.kreweras
      rw [restrict_interleave_odd])).mpr
    exact restrict_interleave_even p q hq

end FreeProbability.NoncrossingPartition

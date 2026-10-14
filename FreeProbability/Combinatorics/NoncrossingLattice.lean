import FreeProbability.Combinatorics.NoncrossingPartition

/-!
# The refinement lattice of noncrossing partitions

Refinement is inherited from equivalence relations. Arbitrary intersections are
noncrossing; hence the noncrossing partitions form a complete lattice. Its join
is the least noncrossing common coarsening, which need not agree with the join in
the lattice of all setoids. This distinction matters in product cumulant formulas.
-/

namespace FreeProbability

variable {n : ℕ}

/-- Arbitrary intersections of noncrossing equivalence relations are noncrossing. -/
theorem IsNoncrossing.sInf (S : Set (Setoid (Fin n)))
    (hS : ∀ p ∈ S, IsNoncrossing p) : IsNoncrossing (sInf S) := by
  intro a b c d hab hbc hcd hac hbd
  rw [Setoid.sInf_iff] at hac hbd ⊢
  intro p hp
  exact hS p hp a b c d hab hbc hcd (hac p hp) (hbd p hp)

namespace NoncrossingPartition

instance : InfSet (NoncrossingPartition n) where
  sInf S := ⟨sInf (Subtype.val '' S), IsNoncrossing.sInf _ (by
    rintro _ ⟨p, _, rfl⟩
    exact p.property)⟩

/-- The complete lattice ordered by block refinement. -/
noncomputable instance : CompleteLattice (NoncrossingPartition n) :=
  completeLatticeOfInf _ (fun S => by
    constructor
    · intro p hp
      change sInf (Subtype.val '' S) ≤ p.val
      exact sInf_le ⟨p, hp, rfl⟩
    · intro q hq
      change q.val ≤ sInf (Subtype.val '' S)
      apply le_sInf
      rintro _ ⟨p, hp, rfl⟩
      exact hq hp)

/-- Refinement means that every pair related in the finer partition remains related. -/
theorem le_iff (p q : NoncrossingPartition n) :
    p ≤ q ↔ ∀ a b, p.val.r a b → q.val.r a b := Iff.rfl

@[simp] theorem sInf_val (S : Set (NoncrossingPartition n)) :
    (sInf S).val = sInf (Subtype.val '' S) := rfl

@[simp] theorem bot_eq_discrete : (⊥ : NoncrossingPartition n) = discrete n := by
  apply le_antisymm
  · exact bot_le
  · intro a b hab
    have he : a = b := hab
    exact he ▸ (⊥ : NoncrossingPartition n).val.refl a

@[simp] theorem top_eq_indiscrete : (⊤ : NoncrossingPartition n) = indiscrete n := by
  apply le_antisymm
  · intro _ _ _
    trivial
  · exact le_top

/-- Meets agree with intersection of the underlying equivalence relations. -/
@[simp] theorem inf_val (p q : NoncrossingPartition n) :
    (p ⊓ q).val = p.val ⊓ q.val := by
  apply le_antisymm
  · exact le_inf (inf_le_left : p ⊓ q ≤ p)
      (inf_le_right : p ⊓ q ≤ q)
  · let r : NoncrossingPartition n := ⟨p.val ⊓ q.val, p.property.inf q.property⟩
    have hr : r ≤ p ⊓ q := le_inf
      (show p.val ⊓ q.val ≤ p.val from inf_le_left)
      (show p.val ⊓ q.val ≤ q.val from inf_le_right)
    exact hr

/-- The least noncrossing equivalence relation containing a prescribed relation. -/
noncomputable def closure (p : Setoid (Fin n)) : NoncrossingPartition n :=
  sInf {q | p ≤ q.val}

theorem le_closure (p : Setoid (Fin n)) : p ≤ (closure p).val := by
  change p ≤ sInf (Subtype.val '' {q : NoncrossingPartition n | p ≤ q.val})
  apply le_sInf
  rintro _ ⟨q, hq, rfl⟩
  exact hq

/-- Universal property of noncrossing closure. -/
theorem closure_le_iff (p : Setoid (Fin n)) (q : NoncrossingPartition n) :
    closure p ≤ q ↔ p ≤ q.val := by
  constructor
  · intro h
    exact le_trans (le_closure p) h
  · intro h
    exact sInf_le h

@[simp] theorem closure_val (p : NoncrossingPartition n) : closure p.val = p := by
  apply le_antisymm
  · exact (closure_le_iff p.val p).mpr le_rfl
  · exact le_closure p.val

/-- The noncrossing join is the noncrossing closure of the ordinary partition join. -/
theorem sup_eq_closure (p q : NoncrossingPartition n) :
    p ⊔ q = closure (p.val ⊔ q.val) := by
  apply le_antisymm
  · apply sup_le
    · change p.val ≤ (closure (p.val ⊔ q.val)).val
      exact le_trans (show p.val ≤ p.val ⊔ q.val from le_sup_left) (le_closure _)
    · change q.val ≤ (closure (p.val ⊔ q.val)).val
      exact le_trans (show q.val ≤ p.val ⊔ q.val from le_sup_right) (le_closure _)
  · apply (closure_le_iff _ _).mpr
    exact sup_le (le_sup_left : p ≤ p ⊔ q) (le_sup_right : q ≤ p ⊔ q)

end NoncrossingPartition
end FreeProbability

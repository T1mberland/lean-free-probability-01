import FreeProbability.Combinatorics.NoncrossingSingletonInsertion
import FreeProbability.Combinatorics.NoncrossingLattice

/-!
# Adjacent contraction of noncrossing partitions

The monotone quotient `Fin.predAbove i` identifies the consecutive positions
`i.castSucc` and `i.succ`. Pullback along this quotient gives an equivalence with
noncrossing partitions in which these positions already belong to one block.
This is the quotient underlying adjacent-product cumulant identities.
-/

namespace FreeProbability

variable {m n : ℕ}

/-- Monotone pullbacks preserve noncrossing, even if neighboring positions coincide. -/
theorem IsNoncrossing.comap_monotone {p : Setoid (Fin n)} (hp : IsNoncrossing p)
    (f : Fin m → Fin n) (hf : Monotone f) : IsNoncrossing (Setoid.comap f p) := by
  intro a b c d hab hbc hcd hac hbd
  change p.r (f a) (f b)
  have hab' := hf hab.le
  have hbc' := hf hbc.le
  have hcd' := hf hcd.le
  by_cases heab : f a = f b
  · exact heab ▸ p.refl (f a)
  by_cases hebc : f b = f c
  · exact hebc.symm ▸ hac
  by_cases hecd : f c = f d
  · exact p.trans hac (p.symm (hecd.symm ▸ hbd))
  exact hp (f a) (f b) (f c) (f d) (lt_of_le_of_ne hab' heab)
    (lt_of_le_of_ne hbc' hebc) (lt_of_le_of_ne hcd' hecd) hac hbd

namespace NoncrossingPartition

/-- Duplicate a position into two consecutive positions in the same block. -/
def duplicate (p : NoncrossingPartition n) (i : Fin n) : NoncrossingPartition (n + 1) :=
  ⟨Setoid.comap i.predAbove p.val, p.property.comap_monotone i.predAbove
    i.predAbove_right_monotone⟩

@[simp] theorem duplicate_rel (p : NoncrossingPartition n) (i : Fin n)
    (a b : Fin (n + 1)) :
    (p.duplicate i).val.r a b ↔ p.val.r (i.predAbove a) (i.predAbove b) := Iff.rfl

/-- The duplicated neighboring positions are related. -/
theorem duplicate_adjacent (p : NoncrossingPartition n) (i : Fin n) :
    (p.duplicate i).val.r i.castSucc i.succ := by
  simp only [duplicate_rel, Fin.predAbove_castSucc_self, Fin.predAbove_succ_self]
  exact p.val.refl i

@[simp] theorem erase_duplicate (p : NoncrossingPartition n) (i : Fin n) :
    (p.duplicate i).erase i.castSucc = p := by
  apply Subtype.ext
  apply Setoid.ext
  intro a b
  change p.val.r (i.predAbove (i.castSucc.succAbove a))
    (i.predAbove (i.castSucc.succAbove b)) ↔ p.val.r a b
  simp only [Fin.predAbove_succAbove]

/-- Duplicating after contraction recovers a partition containing the adjacent pair. -/
theorem duplicate_erase (p : NoncrossingPartition (n + 1)) (i : Fin n)
    (hi : p.val.r i.castSucc i.succ) : (p.erase i.castSucc).duplicate i = p := by
  have hr (a : Fin (n + 1)) : p.val.r a (i.castSucc.succAbove (i.predAbove a)) := by
    by_cases ha : a = i.castSucc
    · subst a
      simpa only [Fin.predAbove_castSucc_self, Fin.succAbove_castSucc_self] using hi
    · rw [Fin.succAbove_predAbove ha]
  apply Subtype.ext
  apply Setoid.ext
  intro a b
  change p.val.r (i.castSucc.succAbove (i.predAbove a))
    (i.castSucc.succAbove (i.predAbove b)) ↔ p.val.r a b
  constructor
  · intro h
    exact p.val.trans (hr a) (p.val.trans h (p.val.symm (hr b)))
  · intro h
    exact p.val.trans (p.val.symm (hr a)) (p.val.trans h (hr b))

/-- The adjacent-contraction bijection. -/
def adjacentContractionEquiv (i : Fin n) : NoncrossingPartition n ≃
    {p : NoncrossingPartition (n + 1) // p.val.r i.castSucc i.succ} where
  toFun p := ⟨p.duplicate i, p.duplicate_adjacent i⟩
  invFun p := p.val.erase i.castSucc
  left_inv p := p.erase_duplicate i
  right_inv p := Subtype.ext (p.val.duplicate_erase i p.property)

theorem duplicate_le_duplicate_iff (p q : NoncrossingPartition n) (i : Fin n) :
    p.duplicate i ≤ q.duplicate i ↔ p ≤ q := by
  constructor
  · intro h a b hab
    have hr := @h (i.castSucc.succAbove a) (i.castSucc.succAbove b)
    simpa only [duplicate_rel, Fin.predAbove_succAbove] using
      hr (by simpa only [duplicate_rel, Fin.predAbove_succAbove] using hab)
  · intro h a b hab
    exact @h _ _ hab

/-- The adjacent contraction bijection also preserves refinement in both directions. -/
def adjacentContractionOrderIso (i : Fin n) : NoncrossingPartition n ≃o
    {p : NoncrossingPartition (n + 1) // p.val.r i.castSucc i.succ} where
  toEquiv := adjacentContractionEquiv i
  map_rel_iff' := by
    intro p q
    exact duplicate_le_duplicate_iff p q i

/-- The interval partition containing exactly the selected adjacent pair. -/
def adjacentPair (i : Fin n) : NoncrossingPartition (n + 1) := (discrete n).duplicate i

/-- Refining above the adjacent pair means the selected neighboring positions are related. -/
theorem adjacentPair_le_iff (p : NoncrossingPartition (n + 1)) (i : Fin n) :
    adjacentPair i ≤ p ↔ p.val.r i.castSucc i.succ := by
  constructor
  · intro h
    exact @h _ _ ((discrete n).duplicate_adjacent i)
  · intro hp
    rw [← p.duplicate_erase i hp]
    exact (duplicate_le_duplicate_iff _ _ i).mpr (by rw [← bot_eq_discrete]; exact bot_le)

/-- Join with the adjacent pair and collapse it, reducing the number of positions by one. -/
noncomputable def contract (p : NoncrossingPartition (n + 1)) (i : Fin n) :
    NoncrossingPartition n := (p ⊔ adjacentPair i).erase i.castSucc

/-- Re-expanding a contraction is precisely the noncrossing join with the adjacent pair. -/
theorem duplicate_contract (p : NoncrossingPartition (n + 1)) (i : Fin n) :
    (p.contract i).duplicate i = p ⊔ adjacentPair i := by
  exact (p ⊔ adjacentPair i).duplicate_erase i
    ((adjacentPair_le_iff _ i).mp le_sup_right)

/-- The quotient universal property underlying adjacent-product partition fibers. -/
theorem contract_le_iff (p : NoncrossingPartition (n + 1))
    (q : NoncrossingPartition n) (i : Fin n) : p.contract i ≤ q ↔ p ≤ q.duplicate i := by
  constructor
  · intro h
    have hd := (duplicate_le_duplicate_iff _ _ i).mpr h
    rw [duplicate_contract] at hd
    exact le_trans le_sup_left hd
  · intro h
    have hj : p ⊔ adjacentPair i ≤ q.duplicate i :=
      sup_le h ((adjacentPair_le_iff _ i).mpr (q.duplicate_adjacent i))
    apply (duplicate_le_duplicate_iff _ _ i).mp
    rw [duplicate_contract]
    exact hj

@[simp] theorem contract_duplicate (p : NoncrossingPartition n) (i : Fin n) :
    (p.duplicate i).contract i = p := by
  apply le_antisymm
  · exact (contract_le_iff _ _ i).mpr le_rfl
  · apply (duplicate_le_duplicate_iff _ _ i).mp
    rw [duplicate_contract]
    exact le_sup_left

end NoncrossingPartition
end FreeProbability

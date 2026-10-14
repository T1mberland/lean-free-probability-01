import FreeProbability.Combinatorics.NoncrossingKrewerasSingleton

/-! # Adjacent joins of inserted singleton partitions -/

namespace FreeProbability.NoncrossingPartition

variable {n : ℕ}

/-- Joining the left inserted singleton to its neighbor duplicates that original block. -/
theorem insertSingleton_sup_adjacentPair_castSucc (p : NoncrossingPartition n) (i : Fin n) :
    p.insertSingleton i.castSucc ⊔ adjacentPair i = p.duplicate i := by
  have hleft : p.insertSingleton i.castSucc ≤ p.duplicate i := by
    intro a b hab
    revert hab
    refine Fin.succAboveCases i.castSucc ?_ (fun u => ?_) a
    · intro hab
      have hb := (p.insertSingleton_rel_at i.castSucc b).mp hab
      subst b
      exact (p.duplicate i).val.refl _
    · intro hab
      revert hab
      refine Fin.succAboveCases i.castSucc ?_ (fun v => ?_) b
      · intro hab
        have hu := (p.insertSingleton_rel_at i.castSucc (i.castSucc.succAbove u)).mp
          ((p.insertSingleton i.castSucc).val.symm hab)
        exact False.elim (i.castSucc.succAbove_ne u hu)
      · intro hab
        simpa only [duplicate_rel, Fin.predAbove_succAbove] using
          (p.insertSingleton_rel_succAbove i.castSucc u v).mp hab
  apply le_antisymm (sup_le hleft ((adjacentPair_le_iff _ i).mpr (p.duplicate_adjacent i)))
  intro a b hab
  let r := p.insertSingleton i.castSucc ⊔ adjacentPair i
  have hsection (a : Fin (n + 1)) : r.val.r a (i.castSucc.succAbove (i.predAbove a)) := by
    by_cases ha : a = i.castSucc
    · subst a
      simp only [Fin.predAbove_castSucc_self, Fin.succAbove_castSucc_self]
      exact (adjacentPair_le_iff r i).mp le_sup_right
    · rw [Fin.succAbove_predAbove ha]
  have hmiddle : r.val.r (i.castSucc.succAbove (i.predAbove a))
      (i.castSucc.succAbove (i.predAbove b)) :=
    (show p.insertSingleton i.castSucc ≤ r from le_sup_left)
      ((p.insertSingleton_rel_succAbove i.castSucc _ _).mpr hab)
  exact r.val.trans (hsection a) (r.val.trans hmiddle (r.val.symm (hsection b)))

/-- The right inserted singleton gives the same duplicated block when joined
with its adjacent left neighbor. -/
theorem insertSingleton_sup_adjacentPair_succ (p : NoncrossingPartition n) (i : Fin n) :
    p.insertSingleton i.succ ⊔ adjacentPair i = p.duplicate i := by
  have hleft : p.insertSingleton i.succ ≤ p.duplicate i := by
    intro a b hab
    revert hab
    refine Fin.succAboveCases i.succ ?_ (fun u => ?_) a
    · intro hab
      have hb := (p.insertSingleton_rel_at i.succ b).mp hab
      subst b
      exact (p.duplicate i).val.refl _
    · intro hab
      revert hab
      refine Fin.succAboveCases i.succ ?_ (fun v => ?_) b
      · intro hab
        have hu := (p.insertSingleton_rel_at i.succ (i.succ.succAbove u)).mp
          ((p.insertSingleton i.succ).val.symm hab)
        exact False.elim (i.succ.succAbove_ne u hu)
      · intro hab
        simpa only [duplicate_rel, predAbove_succ_succAbove] using
          (p.insertSingleton_rel_succAbove i.succ u v).mp hab
  apply le_antisymm (sup_le hleft ((adjacentPair_le_iff _ i).mpr (p.duplicate_adjacent i)))
  intro a b hab
  let r := p.insertSingleton i.succ ⊔ adjacentPair i
  have hsection (a : Fin (n + 1)) : r.val.r a (i.succ.succAbove (i.predAbove a)) := by
    by_cases ha : a = i.succ
    · subst a
      simp only [Fin.predAbove_succ_self, Fin.succAbove_succ_self]
      exact r.val.symm ((adjacentPair_le_iff r i).mp le_sup_right)
    · rw [Fin.succ_succAbove_predAbove ha]
  have hmiddle : r.val.r (i.succ.succAbove (i.predAbove a))
      (i.succ.succAbove (i.predAbove b)) :=
    (show p.insertSingleton i.succ ≤ r from le_sup_left)
      ((p.insertSingleton_rel_succAbove i.succ _ _).mpr hab)
  exact r.val.trans (hsection a) (r.val.trans hmiddle (r.val.symm (hsection b)))

end FreeProbability.NoncrossingPartition

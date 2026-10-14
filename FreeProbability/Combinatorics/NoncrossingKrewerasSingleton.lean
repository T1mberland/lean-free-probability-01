import FreeProbability.Combinatorics.NoncrossingKrewerasAdjacent

/-! # Kreweras transport through noninitial singleton insertion -/

namespace FreeProbability.NoncrossingPartition

variable {n : ℕ}

@[simp] theorem predAbove_succ_succAbove (i a : Fin n) :
    i.predAbove (i.succ.succAbove a) = a := by
  by_cases ha : a ≤ i
  · rw [Fin.succAbove_succ_of_le _ _ ha, Fin.predAbove_castSucc_of_le _ _ ha]
  · rw [Fin.succAbove_succ_of_lt _ _ (lt_of_not_ge ha),
      Fin.predAbove_succ_of_le _ _ (le_of_lt (lt_of_not_ge ha))]

/-- The retained left endpoint of each adjacent quotient fiber is a left
order-adjoint section of the quotient. -/
theorem succ_succAbove_le_iff_le_predAbove (i : Fin n) (a : Fin n) (u : Fin (n + 1)) :
    i.succ.succAbove a ≤ u ↔ a ≤ i.predAbove u := by
  constructor
  · intro h
    simpa only [predAbove_succ_succAbove] using i.predAbove_right_monotone h
  · intro h
    have hu : i.succ.succAbove (i.predAbove u) ≤ u := by
      by_cases he : u = i.succ
      · subst u
        simp only [Fin.predAbove_succ_self, Fin.succAbove_succ_self]
        exact Fin.castSucc_lt_succ.le
      · rw [Fin.succ_succAbove_predAbove he]
    exact (i.succ.strictMono_succAbove.monotone h).trans hu

/-- Chord interval signatures survive deletion of a noninitial original singleton. -/
theorem succ_succAbove_interval_iff (i : Fin n) (u v : Fin n) (a : Fin (n + 1)) :
    (i.succ.succAbove u ≤ a ∧ a < i.succ.succAbove v) ↔
      (u ≤ i.predAbove a ∧ i.predAbove a < v) := by
  rw [succ_succAbove_le_iff_le_predAbove, lt_iff_not_ge, lt_iff_not_ge,
    succ_succAbove_le_iff_le_predAbove]

/-- Inserting a singleton original position after `i` duplicates complementary
position `i`. The boundary position zero is a separate cyclic-rotation case. -/
theorem kreweras_insertSingleton_succ (p : NoncrossingPartition n) (i : Fin n) :
    (p.insertSingleton i.succ).kreweras = p.kreweras.duplicate i := by
  apply Subtype.ext
  apply Setoid.ext
  intro a b
  change (∀ u v, (p.insertSingleton i.succ).val.r u v →
    ((u ≤ a ∧ a < v) ↔ (u ≤ b ∧ b < v))) ↔
    (∀ u v, p.val.r u v → ((u ≤ i.predAbove a ∧ i.predAbove a < v) ↔
      (u ≤ i.predAbove b ∧ i.predAbove b < v)))
  constructor
  · intro h u v huv
    have ht := h (i.succ.succAbove u) (i.succ.succAbove v)
      ((p.insertSingleton_rel_succAbove i.succ u v).mpr huv)
    simpa only [succ_succAbove_interval_iff] using ht
  · intro h u v huv
    by_cases hu : u = i.succ
    · subst u
      have hv : v = i.succ := (p.insertSingleton_rel_at i.succ v).mp huv
      subst v
      constructor <;> intro hbad <;> exact False.elim (not_lt_of_ge hbad.1 hbad.2)
    · have hv : v ≠ i.succ := by
        intro he
        subst v
        exact hu ((p.insertSingleton_rel_at i.succ u).mp ((p.insertSingleton i.succ).val.symm huv))
      have hpr : p.val.r (i.predAbove u) (i.predAbove v) := by
        apply (p.insertSingleton_rel_succAbove i.succ _ _).mp
        simpa only [Fin.succ_succAbove_predAbove hu, Fin.succ_succAbove_predAbove hv] using huv
      have hs := h (i.predAbove u) (i.predAbove v) hpr
      have hua : (u ≤ a ∧ a < v) ↔
          (i.predAbove u ≤ i.predAbove a ∧ i.predAbove a < i.predAbove v) := by
        rw [← Fin.succ_succAbove_predAbove hu, ← Fin.succ_succAbove_predAbove hv]
        simpa only [predAbove_succ_succAbove] using
          succ_succAbove_interval_iff i (i.predAbove u) (i.predAbove v) a
      have hub : (u ≤ b ∧ b < v) ↔
          (i.predAbove u ≤ i.predAbove b ∧ i.predAbove b < i.predAbove v) := by
        rw [← Fin.succ_succAbove_predAbove hu, ← Fin.succ_succAbove_predAbove hv]
        simpa only [predAbove_succ_succAbove] using
          succ_succAbove_interval_iff i (i.predAbove u) (i.predAbove v) b
      exact hua.trans (hs.trans hub.symm)

/-- The exact dual deletion formula at every existing noninitial singleton. -/
theorem kreweras_of_singleton_succ (p : NoncrossingPartition (n + 1)) (i : Fin n)
    (hi : ∀ j, p.val.r i.succ j → j = i.succ) :
    p.kreweras = (p.erase i.succ).kreweras.duplicate i := by
  have he := kreweras_insertSingleton_succ (p.erase i.succ) i
  rwa [p.insertSingleton_erase i.succ hi] at he

end FreeProbability.NoncrossingPartition

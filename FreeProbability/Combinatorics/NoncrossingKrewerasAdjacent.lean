import FreeProbability.Combinatorics.NoncrossingKreweras
import FreeProbability.Combinatorics.NoncrossingAdjacent

/-!
# Kreweras complements and adjacent chord deletion

Duplicating an original position inserts a singleton complementary position.
This exact signature transport is one induction step toward the complementary
block count and the boxed product-cumulant top-fiber characterization.
-/

namespace FreeProbability.NoncrossingPartition

variable {n : ℕ}

/-- The retained right endpoint of each adjacent quotient fiber is a right
order-adjoint section of the monotone quotient. -/
theorem le_succAbove_iff_predAbove_le (i : Fin n) (u : Fin (n + 1)) (a : Fin n) :
    u ≤ i.castSucc.succAbove a ↔ i.predAbove u ≤ a := by
  constructor
  · intro h
    simpa only [Fin.predAbove_succAbove] using i.predAbove_right_monotone h
  · intro h
    have hu : u ≤ i.castSucc.succAbove (i.predAbove u) := by
      by_cases he : u = i.castSucc
      · subst u
        simp only [Fin.predAbove_castSucc_self, Fin.succAbove_castSucc_self]
        exact Fin.castSucc_lt_succ.le
      · rw [Fin.succAbove_predAbove he]
    exact hu.trans (i.castSucc.strictMono_succAbove.monotone h)

/-- Half-open chord signatures transport exactly through deletion of the left
member of an adjacent pair. -/
theorem interval_succAbove_iff (i : Fin n) (u v : Fin (n + 1)) (a : Fin n) :
    (u ≤ i.castSucc.succAbove a ∧ i.castSucc.succAbove a < v) ↔
      (i.predAbove u ≤ a ∧ a < i.predAbove v) := by
  rw [le_succAbove_iff_predAbove_le, lt_iff_not_ge, lt_iff_not_ge,
    le_succAbove_iff_predAbove_le]

/-- An adjacent original chord forces its intervening complementary position
into a singleton block. -/
theorem kreweras_singleton_of_adjacent (p : NoncrossingPartition (n + 1)) (i : Fin n)
    (hi : p.val.r i.castSucc i.succ) :
    ∀ j, p.kreweras.val.r i.castSucc j → j = i.castSucc := by
  intro j hj
  have hsig := hj i.castSucc i.succ hi
  have hinside := hsig.mp ⟨le_rfl, Fin.castSucc_lt_succ⟩
  apply Fin.ext
  change j.val = i.val
  have hle : i.val ≤ j.val := hinside.1
  have hlt : j.val < i.val + 1 := hinside.2
  omega

/-- Deleting the forced complementary singleton after duplicating an original
position gives precisely the original complement. -/
theorem kreweras_duplicate_erase (p : NoncrossingPartition n) (i : Fin n) :
    (p.duplicate i).kreweras.erase i.castSucc = p.kreweras := by
  apply Subtype.ext
  apply Setoid.ext
  intro a b
  change (∀ u v, p.val.r (i.predAbove u) (i.predAbove v) →
    ((u ≤ i.castSucc.succAbove a ∧ i.castSucc.succAbove a < v) ↔
      (u ≤ i.castSucc.succAbove b ∧ i.castSucc.succAbove b < v))) ↔
    (∀ u v, p.val.r u v → ((u ≤ a ∧ a < v) ↔ (u ≤ b ∧ b < v)))
  constructor
  · intro h u v huv
    have ht := h (i.castSucc.succAbove u) (i.castSucc.succAbove v)
      (by simpa only [Fin.predAbove_succAbove] using huv)
    simpa only [interval_succAbove_iff, Fin.predAbove_succAbove] using ht
  · intro h u v huv
    rw [interval_succAbove_iff, interval_succAbove_iff]
    exact h _ _ huv

/-- Exact complement transport: an adjacent original duplication inserts one
complementary singleton at the left duplicated position. -/
theorem kreweras_duplicate (p : NoncrossingPartition n) (i : Fin n) :
    (p.duplicate i).kreweras = p.kreweras.insertSingleton i.castSucc := by
  calc
    _ = ((p.duplicate i).kreweras.erase i.castSucc).insertSingleton i.castSucc :=
      ((p.duplicate i).kreweras.insertSingleton_erase i.castSucc
        ((p.duplicate i).kreweras_singleton_of_adjacent i (p.duplicate_adjacent i))).symm
    _ = _ := by rw [kreweras_duplicate_erase]

/-- The deletion identity applies to every existing adjacent original chord. -/
theorem kreweras_of_adjacent (p : NoncrossingPartition (n + 1)) (i : Fin n)
    (hi : p.val.r i.castSucc i.succ) :
    p.kreweras = (p.erase i.castSucc).kreweras.insertSingleton i.castSucc := by
  have he := kreweras_duplicate (p.erase i.castSucc) i
  rwa [p.duplicate_erase i hi] at he

end FreeProbability.NoncrossingPartition

import FreeProbability.Combinatorics.NoncrossingAdjacentSingletonJoin
import FreeProbability.Combinatorics.NoncrossingReduction
import FreeProbability.Combinatorics.ConsecutiveFusion

/-! # The Kreweras complement joins its original partition to top -/

namespace FreeProbability.NoncrossingPartition

variable {n : ℕ}

@[simp] theorem duplicate_top (i : Fin n) :
    (⊤ : NoncrossingPartition n).duplicate i = ⊤ := by
  rw [top_eq_indiscrete, top_eq_indiscrete]
  apply Subtype.ext
  apply Setoid.ext
  intro a b
  rfl

theorem duplicate_sup_insertSingleton_castSucc (p q : NoncrossingPartition n) (i : Fin n) :
    p.duplicate i ⊔ q.insertSingleton i.castSucc = (p ⊔ q).duplicate i := by
  calc
    _ = (p.duplicate i ⊔ adjacentPair i) ⊔ q.insertSingleton i.castSucc := by
      rw [sup_eq_left.mpr ((adjacentPair_le_iff _ i).mpr (p.duplicate_adjacent i))]
    _ = p.duplicate i ⊔ (q.insertSingleton i.castSucc ⊔ adjacentPair i) := by ac_rfl
    _ = p.duplicate i ⊔ q.duplicate i := by rw [insertSingleton_sup_adjacentPair_castSucc]
    _ = _ := (ConsecutiveFusion.duplicate_sup p q i).symm

theorem insertSingleton_succ_sup_duplicate (p q : NoncrossingPartition n) (i : Fin n) :
    p.insertSingleton i.succ ⊔ q.duplicate i = (p ⊔ q).duplicate i := by
  calc
    _ = p.insertSingleton i.succ ⊔ (q.duplicate i ⊔ adjacentPair i) := by
      rw [sup_eq_left.mpr ((adjacentPair_le_iff _ i).mpr (q.duplicate_adjacent i))]
    _ = (p.insertSingleton i.succ ⊔ adjacentPair i) ⊔ q.duplicate i := by ac_rfl
    _ = p.duplicate i ⊔ q.duplicate i := by rw [insertSingleton_sup_adjacentPair_succ]
    _ = _ := (ConsecutiveFusion.duplicate_sup p q i).symm

/-- Every actual Kreweras complement joins the original partition to top.
This is proved by deletion, not assumed as a complement axiom. -/
theorem sup_kreweras_eq_top (p : NoncrossingPartition n) : p ⊔ p.kreweras = ⊤ := by
  induction n with
  | zero =>
    apply Subtype.ext
    apply Setoid.ext
    intro a
    exact Fin.elim0 a
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      have hp : p = ⊤ := by
        rw [top_eq_indiscrete]
        apply Subtype.ext
        apply Setoid.ext
        intro a b
        constructor
        · intro _
          trivial
        · intro _
          have he : a = b := @Subsingleton.elim (Fin 1) inferInstance a b
          subst b
          exact p.val.refl a
      rw [hp, top_sup_eq]
    rcases p.exists_adjacent_or_singleton_succ (Nat.pos_of_ne_zero hn0) with ⟨i, hi⟩ | ⟨i, hi⟩
    · have hp : p = (p.erase i.castSucc).duplicate i := (p.duplicate_erase i hi).symm
      have hk := p.kreweras_of_adjacent i hi
      calc
        _ = (p.erase i.castSucc).duplicate i ⊔ (p.erase i.castSucc).kreweras.insertSingleton i.castSucc :=
          congrArg₂ (· ⊔ ·) hp hk
        _ = ((p.erase i.castSucc) ⊔ (p.erase i.castSucc).kreweras).duplicate i :=
          duplicate_sup_insertSingleton_castSucc _ _ i
        _ = ⊤ := by rw [ih, duplicate_top]
    · have hp : p = (p.erase i.succ).insertSingleton i.succ := (p.insertSingleton_erase i.succ hi).symm
      have hk := p.kreweras_of_singleton_succ i hi
      calc
        _ = (p.erase i.succ).insertSingleton i.succ ⊔ (p.erase i.succ).kreweras.duplicate i :=
          congrArg₂ (· ⊔ ·) hp hk
        _ = ((p.erase i.succ) ⊔ (p.erase i.succ).kreweras).duplicate i :=
          insertSingleton_succ_sup_duplicate _ _ i
        _ = ⊤ := by rw [ih, duplicate_top]

end FreeProbability.NoncrossingPartition

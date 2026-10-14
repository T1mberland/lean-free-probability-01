import FreeProbability.Combinatorics.ConsecutiveFusionRepresentation
import FreeProbability.Combinatorics.NoncrossingAdjacentMerge
import FreeProbability.Combinatorics.SetoidSurjectivePullback

/-!
# Joins with consecutive interval partitions are already noncrossing

Arbitrary raw joins of noncrossing partitions may cross. For the actual interval
partition of any consecutive fusion, the raw equivalence join is noncrossing:
no additional noncrossing closure identifications are introduced.
-/

namespace FreeProbability.ConsecutiveFusion

variable {n m : ℕ}

/-- The raw equivalence join with a consecutive interval partition agrees
exactly with the noncrossing lattice join. -/
theorem sup_intervalPartition_val (t : ConsecutiveFusion n m) (p : NoncrossingPartition n) :
    (p ⊔ t.intervalPartition).val = p.val ⊔ t.intervalPartition.val := by
  induction t with
  | refl n =>
    change (p ⊔ NoncrossingPartition.discrete n).val = p.val ⊔ (NoncrossingPartition.discrete n).val
    rw [← NoncrossingPartition.bot_eq_discrete, sup_bot_eq]
    have hd : (⊥ : NoncrossingPartition n).val = (⊥ : Setoid (Fin n)) :=
      congrArg Subtype.val NoncrossingPartition.bot_eq_discrete
    rw [hd, sup_bot_eq]
  | cons i t ih =>
    have he : p ⊔ (ConsecutiveFusion.cons i t).intervalPartition =
        (p.contract i ⊔ t.intervalPartition).duplicate i := by
      rw [← (ConsecutiveFusion.cons i t).expand_contract p]
      change (t.expand (t.contract (p.contract i))).duplicate i = _
      rw [t.expand_contract]
    rw [he]
    change Setoid.comap i.predAbove (p.contract i ⊔ t.intervalPartition).val =
      p.val ⊔ (t.intervalPartition.duplicate i).val
    rw [ih]
    rw [setoid_comap_sup_of_surjective i.predAbove
      (fun a => ⟨i.castSucc.succAbove a, Fin.predAbove_succAbove i a⟩)]
    have hc : Setoid.comap i.predAbove (p.contract i).val =
        p.val ⊔ (NoncrossingPartition.adjacentPair i).val := by
      change ((p.contract i).duplicate i).val = _
      rw [p.duplicate_contract, p.sup_adjacentPair_val]
    rw [hc, sup_assoc]
    have hle : (NoncrossingPartition.adjacentPair i).val ≤ (t.intervalPartition.duplicate i).val :=
      (NoncrossingPartition.adjacentPair_le_iff _ i).mpr (t.intervalPartition.duplicate_adjacent i)
    exact congrArg (fun s => p.val ⊔ s) (sup_eq_right.mpr hle)

/-- Consequently the ordinary join relation itself is noncrossing. -/
theorem interval_join_nonCrossing (t : ConsecutiveFusion n m) (p : NoncrossingPartition n) :
    IsNoncrossing (p.val ⊔ t.intervalPartition.val) := by
  rw [← t.sup_intervalPartition_val p]
  exact (p ⊔ t.intervalPartition).property

end FreeProbability.ConsecutiveFusion

namespace FreeProbability.NoncrossingPartition

/-- Joining any noncrossing partition with the raw kernel of a monotone
surjective interval grouping introduces no crossings. -/
theorem sup_ker_nonCrossing {n m : ℕ} (p : NoncrossingPartition n)
    (f : Fin n → Fin m) (hf : Monotone f) (hs : Function.Surjective f) :
    IsNoncrossing (p.val ⊔ Setoid.ker f) := by
  obtain ⟨t, ht⟩ := ConsecutiveFusion.exists_quotient_eq f hf hs
  have hk : t.intervalPartition.val = Setoid.ker f := by
    apply Setoid.ext
    intro a b
    rw [t.intervalPartition_rel, ht]
    rfl
  rw [← hk]
  exact t.interval_join_nonCrossing p

end FreeProbability.NoncrossingPartition

import FreeProbability.Combinatorics.NoncrossingKrewerasJoin
import FreeProbability.Combinatorics.NoncrossingIntervalJoin
import FreeProbability.Combinatorics.OrderedPairProducts

/-! # Raw connectivity of compatible Kreweras interleavings -/

namespace FreeProbability.NoncrossingPartition

variable {n : ℕ}

/-- Collapsing each alternating adjacent pair gives exactly the raw join of
the two constituent equivalence relations. -/
theorem interleave_sup_pairKernel (p q : NoncrossingPartition n) :
    interleaveSetoid p q ⊔ Setoid.ker halfPosition =
      Setoid.comap halfPosition (p.val ⊔ q.val) := by
  apply le_antisymm
  · apply sup_le
    · intro a b hab
      change (p.val ⊔ q.val).r (halfPosition a) (halfPosition b)
      by_cases ha : a.val % 2 = 0
      · exact (show p.val ≤ p.val ⊔ q.val from le_sup_left)
          (by simpa only [ha, ite_true] using hab.2)
      · exact (show q.val ≤ p.val ⊔ q.val from le_sup_right)
          (by simpa only [ha, ite_false] using hab.2)
    · intro a b hab
      change (p.val ⊔ q.val).r (halfPosition a) (halfPosition b)
      change halfPosition a = halfPosition b at hab
      rw [hab]
  · rw [setoid_comap_sup_of_surjective halfPosition halfPosition_surjective]
    apply sup_le
    · intro a b hab
      let r := interleaveSetoid p q ⊔ Setoid.ker halfPosition
      have ha : r.r a (oddPosition (halfPosition a)) :=
        (show Setoid.ker halfPosition ≤ r from le_sup_right) (halfPosition_odd _).symm
      have hb : r.r b (oddPosition (halfPosition b)) :=
        (show Setoid.ker halfPosition ≤ r from le_sup_right) (halfPosition_odd _).symm
      have hm : r.r (oddPosition (halfPosition a)) (oddPosition (halfPosition b)) :=
        (show interleaveSetoid p q ≤ r from le_sup_left)
          ((interleave_odd_odd p q _ _).mpr hab)
      exact r.trans ha (r.trans hm (r.symm hb))
    · intro a b hab
      let r := interleaveSetoid p q ⊔ Setoid.ker halfPosition
      have ha : r.r a (evenPosition (halfPosition a)) :=
        (show Setoid.ker halfPosition ≤ r from le_sup_right) (halfPosition_even _).symm
      have hb : r.r b (evenPosition (halfPosition b)) :=
        (show Setoid.ker halfPosition ≤ r from le_sup_right) (halfPosition_even _).symm
      have hm : r.r (evenPosition (halfPosition a)) (evenPosition (halfPosition b)) :=
        (show interleaveSetoid p q ≤ r from le_sup_left)
          ((interleave_even_even p q _ _).mpr hab)
      exact r.trans ha (r.trans hm (r.symm hb))

/-- For compatible original/complementary partitions, their raw join is already
noncrossing; collapsing alternating pairs introduces no extra closure merges. -/
theorem sup_nonCrossing_of_le_kreweras (p q : NoncrossingPartition n) (hq : q ≤ p.kreweras) :
    IsNoncrossing (p.val ⊔ q.val) := by
  have hd : IsNoncrossing (Setoid.comap halfPosition (p.val ⊔ q.val)) := by
    rw [← interleave_sup_pairKernel]
    exact (p.interleave q hq).sup_ker_nonCrossing halfPosition halfPosition_monotone halfPosition_surjective
  have hr := hd.comap oddOrderEmbedding
  intro a b c d hab hbc hcd hac hbd
  have h := hr a b c d hab hbc hcd
  change (p.val ⊔ q.val).r (halfPosition (oddPosition a)) (halfPosition (oddPosition c)) →
    (p.val ⊔ q.val).r (halfPosition (oddPosition b)) (halfPosition (oddPosition d)) →
      (p.val ⊔ q.val).r (halfPosition (oddPosition a)) (halfPosition (oddPosition b)) at h
  simp only [halfPosition_odd] at h
  exact h hac hbd

/-- The noncrossing and raw joins coincide for every compatible pair. -/
theorem sup_val_of_le_kreweras (p q : NoncrossingPartition n) (hq : q ≤ p.kreweras) :
    (p ⊔ q).val = p.val ⊔ q.val := by
  let r : NoncrossingPartition n := ⟨p.val ⊔ q.val, p.sup_nonCrossing_of_le_kreweras q hq⟩
  have he : p ⊔ q = r := by
    apply le_antisymm
    · exact sup_le (show p.val ≤ p.val ⊔ q.val from le_sup_left)
        (show q.val ≤ p.val ⊔ q.val from le_sup_right)
    · change p.val ⊔ q.val ≤ (p ⊔ q).val
      apply sup_le
      · exact (show p ≤ p ⊔ q from le_sup_left)
      · exact (show q ≤ p ⊔ q from le_sup_right)
  exact congrArg Subtype.val he

/-- The actual ordinary equivalence join of a partition and its complement is top. -/
theorem sup_kreweras_val_eq_top (p : NoncrossingPartition n) :
    p.val ⊔ p.kreweras.val = ⊤ := by
  rw [← p.sup_val_of_le_kreweras p.kreweras le_rfl, p.sup_kreweras_eq_top]
  exact congrArg Subtype.val top_eq_indiscrete

end FreeProbability.NoncrossingPartition

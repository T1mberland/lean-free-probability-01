import FreeProbability.Combinatorics.NoncrossingIncidenceGraph
import FreeProbability.Combinatorics.NoncrossingInterleaveJoin
import FreeProbability.Combinatorics.NoncrossingKrewerasCardinality

/-! # The exact Kreweras top fiber for adjacent alternating products -/

namespace FreeProbability.NoncrossingPartition

variable {n : ℕ}

/-- The consecutive interval partition consisting of each alternating pair. -/
def pairIntervalPartition (n : ℕ) : NoncrossingPartition (2 * n) :=
  ⟨Setoid.ker halfPosition, (discrete n).property.comap_monotone halfPosition halfPosition_monotone⟩

/-- A compatible complementary refinement joins the original raw equivalence
to top exactly when it is the full actual Kreweras complement. -/
theorem sup_val_eq_top_iff_eq_kreweras (p q : NoncrossingPartition n) (hq : q ≤ p.kreweras) :
    p.val ⊔ q.val = ⊤ ↔ q = p.kreweras := by
  constructor
  · intro htop
    by_cases hn : n = 0
    · subst n
      apply Subtype.ext
      apply Setoid.ext
      intro a
      exact Fin.elim0 a
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    by_contra hneq
    have hstrict := card_blocks_lt_of_lt (lt_of_le_of_ne hq hneq)
    have hcount := p.card_blocks_add_kreweras hnpos
    have hbound := p.card_blocks_add_le_of_sup_val_eq_top q hnpos htop
    omega
  · intro he
    subst q
    exact p.sup_kreweras_val_eq_top

private theorem sup_pairInterval_val (r : NoncrossingPartition (2 * n)) :
    (r ⊔ pairIntervalPartition n).val = r.val ⊔ Setoid.ker halfPosition := by
  obtain ⟨t, ht⟩ := ConsecutiveFusion.exists_quotient_eq halfPosition
    halfPosition_monotone halfPosition_surjective
  have he : t.intervalPartition = pairIntervalPartition n := by
    apply Subtype.ext
    apply Setoid.ext
    intro a b
    rw [t.intervalPartition_rel, ht]
    rfl
  rw [← he]
  have hv : t.intervalPartition.val = Setoid.ker halfPosition := congrArg Subtype.val he
  simpa only [hv] using t.sup_intervalPartition_val r

/-- The adjacent-pair top fiber is precisely the full Kreweras complement,
with genuine raw connectivity and actual block counts proved. -/
theorem interleave_sup_pairInterval_eq_top_iff (p q : NoncrossingPartition n)
    (hq : q ≤ p.kreweras) :
    p.interleave q hq ⊔ pairIntervalPartition n = ⊤ ↔ q = p.kreweras := by
  rw [← p.sup_val_eq_top_iff_eq_kreweras q hq]
  constructor
  · intro htop
    have hval := congrArg Subtype.val htop
    rw [sup_pairInterval_val] at hval
    change interleaveSetoid p q ⊔ Setoid.ker halfPosition = (⊤ : NoncrossingPartition (2 * n)).val at hval
    rw [interleave_sup_pairKernel] at hval
    apply Setoid.comap_injective halfPosition halfPosition_surjective
    exact hval.trans (congrArg Subtype.val top_eq_indiscrete)
  · intro htop
    apply Subtype.ext
    rw [sup_pairInterval_val]
    change interleaveSetoid p q ⊔ Setoid.ker halfPosition = (⊤ : NoncrossingPartition (2 * n)).val
    rw [interleave_sup_pairKernel, htop]
    exact (congrArg Subtype.val top_eq_indiscrete).symm

end FreeProbability.NoncrossingPartition

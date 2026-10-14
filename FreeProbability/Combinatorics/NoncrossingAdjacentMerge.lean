import FreeProbability.Combinatorics.NoncrossingAdjacent
import Lean.Elab.Tactic.Omega

/-! # Explicit merging of the blocks at adjacent positions -/

namespace FreeProbability.NoncrossingPartition

variable {n : ℕ}

private theorem crossing_original_anchors (p : NoncrossingPartition n)
    (a b c d u v : Fin n) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hnear : u.val ≤ v.val + 1 ∧ v.val ≤ u.val + 1)
    (hac : p.val.r a c) (hbu : p.val.r b u) (hdv : p.val.r d v) :
    p.val.r a b ∨ p.val.r a u ∨ p.val.r a v := by
  by_cases hau : p.val.r a u
  · exact Or.inr (Or.inl hau)
  by_cases hav : p.val.r a v
  · exact Or.inr (Or.inr hav)
  have hauv : a.val ≠ u.val := fun he => hau (Fin.ext he ▸ p.val.refl a)
  have hcuv : c.val ≠ u.val := fun he => hau ((Fin.ext he : c = u) ▸ hac)
  have havv : a.val ≠ v.val := fun he => hav (Fin.ext he ▸ p.val.refl a)
  have hcvv : c.val ≠ v.val := fun he => hav ((Fin.ext he : c = v) ▸ hac)
  rcases lt_trichotomy u a with hua | hua | hau'
  · have hrel := p.property u a b c hua hab hbc (p.val.symm hbu) hac
    exact Or.inr (Or.inl (p.val.symm hrel))
  · exact False.elim (hauv (congrArg Fin.val hua.symm))
  · rcases lt_trichotomy u c with huc | huc | hcu
    · have hav' : a < v := by
        have hauval : a.val < u.val := hau'
        change a.val < v.val
        omega
      have hvc : v < c := by
        have hucval : u.val < c.val := huc
        change v.val < c.val
        omega
      exact Or.inr (Or.inr (p.property a v c d hav' hvc hcd hac (p.val.symm hdv)))
    · exact False.elim (hcuv (congrArg Fin.val huc.symm))
    · exact Or.inl (p.property a b c u hab hbc hcu hac hbu)

private theorem crossing_anchors_original (p : NoncrossingPartition n)
    (a b c d u v : Fin n) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hnear : u.val ≤ v.val + 1 ∧ v.val ≤ u.val + 1)
    (hau : p.val.r a u) (hcv : p.val.r c v) (hbd : p.val.r b d) :
    p.val.r a b ∨ p.val.r b u ∨ p.val.r b v := by
  by_cases hbu : p.val.r b u
  · exact Or.inr (Or.inl hbu)
  by_cases hbv : p.val.r b v
  · exact Or.inr (Or.inr hbv)
  have hbuv : b.val ≠ u.val := fun he => hbu (Fin.ext he ▸ p.val.refl b)
  have hduv : d.val ≠ u.val := fun he => hbu ((Fin.ext he : d = u) ▸ hbd)
  have hbvv : b.val ≠ v.val := fun he => hbv (Fin.ext he ▸ p.val.refl b)
  have hdvv : d.val ≠ v.val := fun he => hbv ((Fin.ext he : d = v) ▸ hbd)
  rcases lt_trichotomy u b with hub | hub | hbu'
  · have hvb : v < b := by
      have hubval : u.val < b.val := hub
      change v.val < b.val
      omega
    exact Or.inr (Or.inr (p.val.symm
      (p.property v b c d hvb hbc hcd (p.val.symm hcv) hbd)))
  · exact False.elim (hbuv (congrArg Fin.val hub.symm))
  · rcases lt_trichotomy u d with hud | hud | hdu
    · exact Or.inl (p.property a b u d hab hbu' hud hau hbd)
    · exact False.elim (hduv (congrArg Fin.val hud.symm))
    · have hdv : d < v := by
        have hduval : d.val < u.val := hdu
        change d.val < v.val
        omega
      have hbcRel := p.property b c d v hbc hcd hdv hbd hcv
      exact Or.inr (Or.inr (p.val.trans hbcRel hcv))

/-- Explicitly merge the two equivalence classes meeting the selected positions. -/
def mergeSetoid (p : NoncrossingPartition n) (u v : Fin n) : Setoid (Fin n) where
  r a b := p.val.r a b ∨
    ((p.val.r a u ∨ p.val.r a v) ∧ (p.val.r b u ∨ p.val.r b v))
  iseqv := {
    refl := fun a => Or.inl (p.val.refl a)
    symm := by
      intro a b h
      rcases h with h | ⟨ha, hb⟩
      · exact Or.inl (p.val.symm h)
      · exact Or.inr ⟨hb, ha⟩
    trans := by
      intro a b c hab hbc
      rcases hab with hab | ⟨ha, hb⟩ <;> rcases hbc with hbc | ⟨hb', hc⟩
      · exact Or.inl (p.val.trans hab hbc)
      · refine Or.inr ⟨?_, hc⟩
        exact hb'.imp (p.val.trans hab) (p.val.trans hab)
      · refine Or.inr ⟨ha, ?_⟩
        exact hb.imp (p.val.trans (p.val.symm hbc)) (p.val.trans (p.val.symm hbc))
      · exact Or.inr ⟨ha, hc⟩ }

/-- Merging classes meeting consecutive positions introduces no crossing. -/
theorem mergeSetoid_nonCrossing (p : NoncrossingPartition n) (u v : Fin n)
    (huv : u.val + 1 = v.val) : IsNoncrossing (p.mergeSetoid u v) := by
  intro a b c d hab hbc hcd hac hbd
  have hnear : u.val ≤ v.val + 1 ∧ v.val ≤ u.val + 1 := by omega
  change p.val.r a c ∨ ((p.val.r a u ∨ p.val.r a v) ∧
    (p.val.r c u ∨ p.val.r c v)) at hac
  change p.val.r b d ∨ ((p.val.r b u ∨ p.val.r b v) ∧
    (p.val.r d u ∨ p.val.r d v)) at hbd
  change p.val.r a b ∨ ((p.val.r a u ∨ p.val.r a v) ∧
    (p.val.r b u ∨ p.val.r b v))
  rcases hac with hac | ⟨ha, hc⟩ <;> rcases hbd with hbd | ⟨hb, hd⟩
  · exact Or.inl (p.property a b c d hab hbc hcd hac hbd)
  · rcases hb with hbu | hbv <;> rcases hd with hdu | hdv
    · exact Or.inl (p.property a b c d hab hbc hcd hac
        (p.val.trans hbu (p.val.symm hdu)))
    · rcases crossing_original_anchors p a b c d u v hab hbc hcd hnear hac hbu hdv with
        h | h | h
      · exact Or.inl h
      · exact Or.inr ⟨Or.inl h, Or.inl hbu⟩
      · exact Or.inr ⟨Or.inr h, Or.inl hbu⟩
    · rcases crossing_original_anchors p a b c d v u hab hbc hcd hnear.symm hac hbv hdu with
        h | h | h
      · exact Or.inl h
      · exact Or.inr ⟨Or.inr h, Or.inr hbv⟩
      · exact Or.inr ⟨Or.inl h, Or.inr hbv⟩
    · exact Or.inl (p.property a b c d hab hbc hcd hac
        (p.val.trans hbv (p.val.symm hdv)))
  · rcases ha with hau | hav <;> rcases hc with hcu | hcv
    · exact Or.inl (p.property a b c d hab hbc hcd
        (p.val.trans hau (p.val.symm hcu)) hbd)
    · rcases crossing_anchors_original p a b c d u v hab hbc hcd hnear hau hcv hbd with
        h | h | h
      · exact Or.inl h
      · exact Or.inr ⟨Or.inl hau, Or.inl h⟩
      · exact Or.inr ⟨Or.inl hau, Or.inr h⟩
    · rcases crossing_anchors_original p a b c d v u hab hbc hcd hnear.symm hav hcu hbd with
        h | h | h
      · exact Or.inl h
      · exact Or.inr ⟨Or.inr hav, Or.inr h⟩
      · exact Or.inr ⟨Or.inr hav, Or.inl h⟩
    · exact Or.inl (p.property a b c d hab hbc hcd
        (p.val.trans hav (p.val.symm hcv)) hbd)
  · exact Or.inr ⟨ha, hb⟩

/-- Merging the classes at the selected adjacent positions as a noncrossing partition. -/
def mergeAdjacent (p : NoncrossingPartition (n + 1)) (i : Fin n) :
    NoncrossingPartition (n + 1) :=
  ⟨p.mergeSetoid i.castSucc i.succ, p.mergeSetoid_nonCrossing _ _ (by simp)⟩

/-- The explicit two-class merge is exactly the noncrossing join with the adjacent pair. -/
theorem mergeAdjacent_eq_sup (p : NoncrossingPartition (n + 1)) (i : Fin n) :
    p.mergeAdjacent i = p ⊔ adjacentPair i := by
  apply le_antisymm
  · intro a b hab
    change p.val.r a b ∨ ((p.val.r a i.castSucc ∨ p.val.r a i.succ) ∧
      (p.val.r b i.castSucc ∨ p.val.r b i.succ)) at hab
    let q := p ⊔ adjacentPair i
    have hp : p ≤ q := le_sup_left
    have hpair : q.val.r i.castSucc i.succ :=
      (adjacentPair_le_iff q i).mp le_sup_right
    have hanchor (a : Fin (n + 1)) (ha : p.val.r a i.castSucc ∨ p.val.r a i.succ) :
        q.val.r a i.castSucc := by
      rcases ha with h | h
      · exact hp h
      · exact q.val.trans (hp h) (q.val.symm hpair)
    rcases hab with h | ⟨ha, hb⟩
    · exact hp h
    · exact q.val.trans (hanchor a ha) (q.val.symm (hanchor b hb))
  · apply sup_le
    · intro a b h
      exact Or.inl h
    · apply (adjacentPair_le_iff _ i).mpr
      exact Or.inr ⟨Or.inl (p.val.refl _), Or.inr (p.val.refl _)⟩

/-- For a single adjacent pair, the raw partition join is already noncrossing. -/
theorem sup_adjacentPair_val (p : NoncrossingPartition (n + 1)) (i : Fin n) :
    (p ⊔ adjacentPair i).val = p.val ⊔ (adjacentPair i).val := by
  apply le_antisymm
  · rw [← mergeAdjacent_eq_sup]
    intro a b hab
    change p.val.r a b ∨ ((p.val.r a i.castSucc ∨ p.val.r a i.succ) ∧
      (p.val.r b i.castSucc ∨ p.val.r b i.succ)) at hab
    let q := p.val ⊔ (adjacentPair i).val
    have hp : p.val ≤ q := le_sup_left
    have hpair : q.r i.castSucc i.succ := (le_sup_right : (adjacentPair i).val ≤ q) ((discrete n).duplicate_adjacent i)
    have hanchor (a : Fin (n + 1)) (ha : p.val.r a i.castSucc ∨ p.val.r a i.succ) :
        q.r a i.castSucc := by
      rcases ha with h | h
      · exact hp h
      · exact q.trans (hp h) (q.symm hpair)
    rcases hab with h | ⟨ha, hb⟩
    · exact hp h
    · exact q.trans (hanchor a ha) (q.symm (hanchor b hb))
  · exact sup_le (le_sup_left : p ≤ p ⊔ adjacentPair i)
      (le_sup_right : adjacentPair i ≤ p ⊔ adjacentPair i)

/-- A partition becomes indiscrete after adjoining the adjacent pair exactly when
all its blocks meet one of the two selected positions. -/
theorem sup_adjacentPair_eq_top_iff (p : NoncrossingPartition (n + 1)) (i : Fin n) :
    p ⊔ adjacentPair i = ⊤ ↔
      ∀ a, p.val.r a i.castSucc ∨ p.val.r a i.succ := by
  rw [← mergeAdjacent_eq_sup]
  constructor
  · intro he a
    have h : (p.mergeAdjacent i).val.r a i.castSucc := by
      rw [he, top_eq_indiscrete]
      trivial
    rcases h with h | ⟨ha, _⟩
    · exact Or.inl h
    · exact ha
  · intro h
    apply le_antisymm le_top
    intro a b _
    exact Or.inr ⟨h a, h b⟩

/-- A top adjacent-product fiber has at most two blocks. -/
theorem card_blocks_le_two_of_sup_adjacentPair_eq_top
    (p : NoncrossingPartition (n + 1)) (i : Fin n)
    (hp : p ⊔ adjacentPair i = ⊤) : p.blocks.card ≤ 2 := by
  classical
  obtain ⟨s, ⟨hs, his⟩, _⟩ := p.existsUnique_block i.castSucc
  obtain ⟨t, ⟨ht, hit⟩, _⟩ := p.existsUnique_block i.succ
  have hsub : p.blocks ⊆ {s, t} := by
    intro u hu
    obtain ⟨a, hau⟩ := p.block_nonempty hu
    rcases (p.sup_adjacentPair_eq_top_iff i).mp hp a with h | h
    · have hiu := (p.rel_iff_mem_block hu hau i.castSucc).mp h
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inl
        ((p.existsUnique_block i.castSucc).unique ⟨hu, hiu⟩ ⟨hs, his⟩)
    · have hiu := (p.rel_iff_mem_block hu hau i.succ).mp h
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr
        ((p.existsUnique_block i.succ).unique ⟨hu, hiu⟩ ⟨ht, hit⟩)
  have hc := Finset.card_le_card hsub
  rcases Finset.card_pair_eq_one_or_two (a := s) (b := t) with h | h <;> omega

/-- Monochromatic blocks in a top adjacent-product fiber force a monochromatic word
when the two multiplied coordinates have the same color. -/
theorem monochromatic_of_sup_adjacentPair_eq_top {I : Type*}
    (p : NoncrossingPartition (n + 1)) (i : Fin n) (color : Fin (n + 1) → I)
    (hp : p ⊔ adjacentPair i = ⊤) (hi : color i.castSucc = color i.succ)
    (hmono : ∀ a b, p.val.r a b → color a = color b) :
    ∀ a, color a = color i.castSucc := by
  intro a
  rcases (p.sup_adjacentPair_eq_top_iff i).mp hp a with h | h
  · exact hmono _ _ h
  · exact (hmono _ _ h).trans hi.symm

end FreeProbability.NoncrossingPartition

import FreeProbability.Combinatorics.NoncrossingRestriction

/-!
# Refining a single noncrossing block

Replace one block by an arbitrary noncrossing partition of its ordered positions,
leaving every other block unchanged. Noncrossing is preserved because any crossing
between the new blocks lies within the original block. Restriction recovers the
chosen local partition exactly.
-/

namespace FreeProbability.NoncrossingPartition

variable {n : ℕ}

private def refinementSetoid (p : NoncrossingPartition n) (s : Finset (Fin n))
    (hs : s ∈ p.blocks) (r : NoncrossingPartition s.card) : Setoid (Fin n) where
  r a b := p.val.r a b ∧ ∀ (ha : a ∈ s) (hb : b ∈ s),
    r.val.r ((s.orderIsoOfFin rfl).symm ⟨a, ha⟩) ((s.orderIsoOfFin rfl).symm ⟨b, hb⟩)
  iseqv := {
    refl := by
      intro a
      exact ⟨p.val.refl a, fun _ _ => r.val.refl _⟩
    symm := by
      intro a b h
      exact ⟨p.val.symm h.1, fun ha hb => r.val.symm (h.2 hb ha)⟩
    trans := by
      intro a b c hab hbc
      refine ⟨p.val.trans hab.1 hbc.1, ?_⟩
      intro ha hc
      have hb : b ∈ s := (p.rel_iff_mem_block hs ha b).mp hab.1
      exact r.val.trans (hab.2 ha hb) (hbc.2 hb hc) }

private theorem refinementSetoid_nonCrossing (p : NoncrossingPartition n)
    (s : Finset (Fin n)) (hs : s ∈ p.blocks) (r : NoncrossingPartition s.card) :
    IsNoncrossing (refinementSetoid p s hs r) := by
  intro a b c d hab hbc hcd hac hbd
  refine ⟨p.property a b c d hab hbc hcd hac.1 hbd.1, ?_⟩
  intro ha hb
  have hc : c ∈ s := (p.rel_iff_mem_block hs ha c).mp hac.1
  have hd : d ∈ s := (p.rel_iff_mem_block hs hb d).mp hbd.1
  have hab' : (s.orderIsoOfFin rfl).symm ⟨a, ha⟩ <
      (s.orderIsoOfFin rfl).symm ⟨b, hb⟩ := (s.orderIsoOfFin rfl).symm.lt_iff_lt.mpr hab
  have hbc' : (s.orderIsoOfFin rfl).symm ⟨b, hb⟩ <
      (s.orderIsoOfFin rfl).symm ⟨c, hc⟩ := (s.orderIsoOfFin rfl).symm.lt_iff_lt.mpr hbc
  have hcd' : (s.orderIsoOfFin rfl).symm ⟨c, hc⟩ <
      (s.orderIsoOfFin rfl).symm ⟨d, hd⟩ := (s.orderIsoOfFin rfl).symm.lt_iff_lt.mpr hcd
  exact r.property _ _ _ _ hab' hbc' hcd' (hac.2 ha hc) (hbd.2 hb hd)

/-- Replace an actual block with a chosen noncrossing partition of its positions. -/
def refineBlock (p : NoncrossingPartition n) (s : Finset (Fin n)) (hs : s ∈ p.blocks)
    (r : NoncrossingPartition s.card) : NoncrossingPartition n :=
  ⟨refinementSetoid p s hs r, refinementSetoid_nonCrossing p s hs r⟩

/-- Block replacement is a refinement of the original partition. -/
theorem refineBlock_le (p : NoncrossingPartition n) (s : Finset (Fin n))
    (hs : s ∈ p.blocks) (r : NoncrossingPartition s.card) : p.refineBlock s hs r ≤ p :=
  by intro a b h; exact h.1

/-- The chosen local partition is recovered by restricting to the refined block. -/
@[simp] theorem restrict_refineBlock (p : NoncrossingPartition n) (s : Finset (Fin n))
    (hs : s ∈ p.blocks) (r : NoncrossingPartition s.card) :
    (p.refineBlock s hs r).restrict (s.orderEmbOfFin rfl) = r := by
  apply Subtype.ext
  apply Setoid.ext
  intro a b
  have hindex (j : Fin s.card) (hj : s.orderEmbOfFin rfl j ∈ s) :
      (s.orderIsoOfFin rfl).symm ⟨s.orderEmbOfFin rfl j, hj⟩ = j := by
    change (s.orderIsoOfFin rfl).symm ((s.orderIsoOfFin rfl) j) = j
    exact (s.orderIsoOfFin rfl).symm_apply_apply j
  constructor
  · intro h
    have hlocal := h.2 (s.orderEmbOfFin_mem rfl a) (s.orderEmbOfFin_mem rfl b)
    simpa only [hindex] using hlocal
  · intro h
    refine ⟨(p.same_block_iff _ _).mp ⟨s, hs, s.orderEmbOfFin_mem rfl a,
      s.orderEmbOfFin_mem rfl b⟩, ?_⟩
    intro ha hb
    simpa only [hindex] using h

/-- Relations outside the replaced block are unchanged. -/
theorem refineBlock_rel_of_not_mem (p : NoncrossingPartition n) (s : Finset (Fin n))
    (hs : s ∈ p.blocks) (r : NoncrossingPartition s.card) (a b : Fin n) (ha : a ∉ s) :
    (p.refineBlock s hs r).val.r a b ↔ p.val.r a b := by
  constructor
  · exact And.left
  · intro h
    exact ⟨h, fun has _ => False.elim (ha has)⟩

/-- Inside the replaced block, the relation is exactly the chosen local relation. -/
theorem refineBlock_rel_inside (p : NoncrossingPartition n) (s : Finset (Fin n))
    (hs : s ∈ p.blocks) (r : NoncrossingPartition s.card) (a b : Fin n)
    (ha : a ∈ s) (hb : b ∈ s) :
    (p.refineBlock s hs r).val.r a b ↔
      r.val.r ((s.orderIsoOfFin rfl).symm ⟨a, ha⟩) ((s.orderIsoOfFin rfl).symm ⟨b, hb⟩) := by
  constructor
  · intro h
    exact h.2 ha hb
  · intro h
    exact ⟨(p.same_block_iff a b).mp ⟨s, hs, ha, hb⟩, fun _ _ => h⟩

/-- Distinct local refinements give distinct global refinements. -/
theorem refineBlock_injective (p : NoncrossingPartition n) (s : Finset (Fin n))
    (hs : s ∈ p.blocks) : Function.Injective (p.refineBlock s hs) := by
  intro r t h
  have hr := congrArg (fun q => q.restrict (s.orderEmbOfFin rfl)) h
  simpa only [restrict_refineBlock] using hr

/-- Replacing a block by the indiscrete partition changes nothing. -/
@[simp] theorem refineBlock_indiscrete (p : NoncrossingPartition n) (s : Finset (Fin n))
    (hs : s ∈ p.blocks) : p.refineBlock s hs (indiscrete s.card) = p := by
  apply Subtype.ext
  apply Setoid.ext
  intro a b
  exact ⟨And.left, fun h => ⟨h, fun _ _ => trivial⟩⟩

end FreeProbability.NoncrossingPartition

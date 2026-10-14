import FreeProbability.Combinatorics.NoncrossingBlockRefinement
import FreeProbability.Combinatorics.NoncrossingLattice

/-!
# Refinement intervals as products of noncrossing partition lattices

A refinement of a noncrossing partition is uniquely specified by independent
noncrossing refinements of its ordered blocks. This is a genuine equivalence,
with explicit simultaneous blockwise construction and restriction inverses.
-/

namespace FreeProbability.NoncrossingPartition

variable {n : ℕ}

/-- A chosen noncrossing partition on each ordered block. -/
abbrev BlockRefinements (p : NoncrossingPartition n) :=
  ∀ s : {s // s ∈ p.blocks}, NoncrossingPartition s.val.card

private def blockwiseSetoid (p : NoncrossingPartition n) (R : BlockRefinements p) :
    Setoid (Fin n) where
  r a b := p.val.r a b ∧ ∀ (s : {s // s ∈ p.blocks}) (ha : a ∈ s.val) (hb : b ∈ s.val),
    (R s).val.r ((s.val.orderIsoOfFin rfl).symm ⟨a, ha⟩)
      ((s.val.orderIsoOfFin rfl).symm ⟨b, hb⟩)
  iseqv := {
    refl := fun a => ⟨p.val.refl a, fun s _ _ => (R s).val.refl _⟩
    symm := by
      intro a b h
      exact ⟨p.val.symm h.1, fun s ha hb => (R s).val.symm (h.2 s hb ha)⟩
    trans := by
      intro a b c hab hbc
      refine ⟨p.val.trans hab.1 hbc.1, ?_⟩
      intro s ha hc
      have hb : b ∈ s.val := (p.rel_iff_mem_block s.property ha b).mp hab.1
      exact (R s).val.trans (hab.2 s ha hb) (hbc.2 s hb hc) }

private theorem blockwiseSetoid_nonCrossing (p : NoncrossingPartition n) (R : BlockRefinements p) :
    IsNoncrossing (blockwiseSetoid p R) := by
  intro a b c d hab hbc hcd hac hbd
  refine ⟨p.property a b c d hab hbc hcd hac.1 hbd.1, ?_⟩
  intro s ha hb
  have hc : c ∈ s.val := (p.rel_iff_mem_block s.property ha c).mp hac.1
  have hd : d ∈ s.val := (p.rel_iff_mem_block s.property hb d).mp hbd.1
  exact (R s).property _ _ _ _ ((s.val.orderIsoOfFin rfl).symm.lt_iff_lt.mpr hab)
    ((s.val.orderIsoOfFin rfl).symm.lt_iff_lt.mpr hbc)
    ((s.val.orderIsoOfFin rfl).symm.lt_iff_lt.mpr hcd) (hac.2 s ha hc) (hbd.2 s hb hd)

/-- Simultaneously refine all blocks of a noncrossing partition. -/
def refineBlocks (p : NoncrossingPartition n) (R : BlockRefinements p) : NoncrossingPartition n :=
  ⟨blockwiseSetoid p R, blockwiseSetoid_nonCrossing p R⟩

theorem refineBlocks_le (p : NoncrossingPartition n) (R : BlockRefinements p) : p.refineBlocks R ≤ p := by
  intro a b h
  exact h.1

private theorem block_index_position (s : Finset (Fin n)) (a : Fin n) (ha : a ∈ s) :
    s.orderEmbOfFin rfl ((s.orderIsoOfFin rfl).symm ⟨a, ha⟩) = a :=
  congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨a, ha⟩)

private theorem block_position_index (s : Finset (Fin n)) (a : Fin s.card)
    (ha : s.orderEmbOfFin rfl a ∈ s) :
    (s.orderIsoOfFin rfl).symm ⟨s.orderEmbOfFin rfl a, ha⟩ = a := by
  change (s.orderIsoOfFin rfl).symm ((s.orderIsoOfFin rfl) a) = a
  exact (s.orderIsoOfFin rfl).symm_apply_apply a

/-- Restricting the simultaneous refinement to a parent block recovers its local choice. -/
@[simp] theorem restrict_refineBlocks (p : NoncrossingPartition n) (R : BlockRefinements p)
    (s : {s // s ∈ p.blocks}) : (p.refineBlocks R).restrict (s.val.orderEmbOfFin rfl) = R s := by
  apply Subtype.ext
  apply Setoid.ext
  intro a b
  constructor
  · intro h
    have hlocal := h.2 s (s.val.orderEmbOfFin_mem rfl a) (s.val.orderEmbOfFin_mem rfl b)
    simpa only [block_position_index] using hlocal
  · intro h
    refine ⟨(p.same_block_iff _ _).mp ⟨s.val, s.property, s.val.orderEmbOfFin_mem rfl a,
      s.val.orderEmbOfFin_mem rfl b⟩, ?_⟩
    intro t ha hb
    have hts : t = s := Subtype.ext ((p.existsUnique_block (s.val.orderEmbOfFin rfl a)).unique
      ⟨t.property, ha⟩ ⟨s.property, s.val.orderEmbOfFin_mem rfl a⟩)
    subst t
    simpa only [block_position_index] using h

/-- A refinement is recovered exactly from its restrictions to all parent blocks. -/
@[simp] theorem refineBlocks_restrict {p q : NoncrossingPartition n} (hqp : q ≤ p) :
    p.refineBlocks (fun s => q.restrict (s.val.orderEmbOfFin rfl)) = q := by
  apply Subtype.ext
  apply Setoid.ext
  intro a b
  constructor
  · intro h
    obtain ⟨s, hs, has, hbs⟩ := (p.same_block_iff a b).mpr h.1
    have hlocal := h.2 ⟨s, hs⟩ has hbs
    change q.val.r (s.orderEmbOfFin rfl ((s.orderIsoOfFin rfl).symm ⟨a, has⟩))
      (s.orderEmbOfFin rfl ((s.orderIsoOfFin rfl).symm ⟨b, hbs⟩)) at hlocal
    simpa only [block_index_position] using hlocal
  · intro h
    refine ⟨hqp h, ?_⟩
    intro s ha hb
    change q.val.r (s.val.orderEmbOfFin rfl ((s.val.orderIsoOfFin rfl).symm ⟨a, ha⟩))
      (s.val.orderEmbOfFin rfl ((s.val.orderIsoOfFin rfl).symm ⟨b, hb⟩))
    simpa only [block_index_position] using h

/-- The entire lower refinement interval is the product of local noncrossing partitions. -/
def refinementEquiv (p : NoncrossingPartition n) : {q : NoncrossingPartition n // q ≤ p} ≃
    BlockRefinements p where
  toFun q s := q.val.restrict (s.val.orderEmbOfFin rfl)
  invFun R := ⟨p.refineBlocks R, p.refineBlocks_le R⟩
  left_inv q := Subtype.ext (refineBlocks_restrict q.property)
  right_inv R := by funext s; exact p.restrict_refineBlocks R s

/-- Simultaneous refinement preserves and reflects coordinatewise local refinement. -/
theorem refineBlocks_le_iff (p : NoncrossingPartition n) (R S : BlockRefinements p) :
    p.refineBlocks R ≤ p.refineBlocks S ↔ ∀ s, R s ≤ S s := by
  constructor
  · intro h s
    have hr : (p.refineBlocks R).restrict (s.val.orderEmbOfFin rfl) ≤
        (p.refineBlocks S).restrict (s.val.orderEmbOfFin rfl) := by
      intro a b hab
      exact h hab
    simpa only [restrict_refineBlocks] using hr
  · intro h a b hab
    exact ⟨hab.1, fun s ha hb => h s (hab.2 s ha hb)⟩

/-- The lower interval is order-isomorphic to the product of the block lattices. -/
def blockRefinementOrderIso (p : NoncrossingPartition n) : BlockRefinements p ≃o
    {q : NoncrossingPartition n // q ≤ p} where
  toEquiv := (p.refinementEquiv).symm
  map_rel_iff' := by
    intro R S
    exact p.refineBlocks_le_iff R S

end FreeProbability.NoncrossingPartition

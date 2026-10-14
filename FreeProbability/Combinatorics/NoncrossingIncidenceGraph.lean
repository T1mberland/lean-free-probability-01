import FreeProbability.Combinatorics.NoncrossingBlockMap
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! # Block-incidence connectivity and cardinality -/

namespace FreeProbability.NoncrossingPartition

variable {n : ℕ}

/-- Vertices are actual blocks of the two partitions, with distinct parity tags. -/
abbrev IncidenceVertices (p q : NoncrossingPartition n) :=
  Sum {s // s ∈ p.blocks} {t // t ∈ q.blocks}

/-- An original index joins its containing blocks in the bipartite incidence graph. -/
def incidenceGraph (p q : NoncrossingPartition n) : SimpleGraph (IncidenceVertices p q) where
  Adj u v := match u, v with
    | .inl s, .inr t => ∃ i, i ∈ s.val ∧ i ∈ t.val
    | .inr t, .inl s => ∃ i, i ∈ s.val ∧ i ∈ t.val
    | _, _ => False
  symm := ⟨by intro u v; cases u <;> cases v <;> exact id⟩
  loopless := ⟨by intro u; cases u <;> exact not_false⟩

private theorem blockOf_eq_of_mem (p : NoncrossingPartition n) (s : {s // s ∈ p.blocks})
    {i : Fin n} (hi : i ∈ s.val) : p.blockOf i = s := by
  apply Subtype.ext
  exact (p.existsUnique_block i).unique ⟨(p.blockOf i).property, p.mem_blockOf i⟩ ⟨s.property, hi⟩

private theorem incidence_index_adj (p q : NoncrossingPartition n) (i : Fin n) :
    (p.incidenceGraph q).Adj (.inl (p.blockOf i)) (.inr (q.blockOf i)) :=
  ⟨i, p.mem_blockOf i, q.mem_blockOf i⟩

/-- Raw equivalence-join connectivity gives genuine incidence-graph connectivity. -/
theorem incidenceGraph_connected_of_sup_val_eq_top (p q : NoncrossingPartition n)
    (hn : 0 < n) (hjoin : p.val ⊔ q.val = ⊤) : (p.incidenceGraph q).Connected := by
  let G := p.incidenceGraph q
  have hindices (a b : Fin n) : G.Reachable (.inl (p.blockOf a)) (.inl (p.blockOf b)) := by
    have hab : (p.val ⊔ q.val).r a b := by rw [hjoin]; trivial
    rw [Setoid.sup_eq_eqvGen] at hab
    induction hab with
    | rel a b hab =>
      rcases hab with hp | hq
      · rw [(p.blockOf_eq_iff a b).mpr hp]
      · have he := (q.blockOf_eq_iff a b).mpr hq
        exact (incidence_index_adj p q a).reachable.trans
          (by rw [he]; exact (incidence_index_adj p q b).reachable.symm)
    | refl _ => exact SimpleGraph.Reachable.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  have hvertex (v : IncidenceVertices p q) :
      ∃ i : Fin n, G.Reachable v (.inl (p.blockOf i)) := by
    cases v with
    | inl s =>
      obtain ⟨i, hi⟩ := p.block_nonempty s.property
      refine ⟨i, ?_⟩
      rw [blockOf_eq_of_mem p s hi]
    | inr t =>
      obtain ⟨i, hi⟩ := q.block_nonempty t.property
      refine ⟨i, ?_⟩
      have he := blockOf_eq_of_mem q t hi
      rw [← he]
      exact (incidence_index_adj p q i).reachable.symm
  let : Nonempty (IncidenceVertices p q) := ⟨.inl (p.blockOf ⟨0, hn⟩)⟩
  refine ⟨?_⟩
  intro u v
  obtain ⟨a, ha⟩ := hvertex u
  obtain ⟨b, hb⟩ := hvertex v
  exact ha.trans ((hindices a b).trans hb.symm)

/-- The number of distinct incidence edges is bounded by the number of original indices. -/
theorem incidenceGraph_card_edges_le (p q : NoncrossingPartition n) :
    Nat.card (p.incidenceGraph q).edgeSet ≤ n := by
  classical
  let edge : Fin n → (p.incidenceGraph q).edgeSet := fun i =>
    ⟨s(Sum.inl (p.blockOf i), Sum.inr (q.blockOf i)),
      (p.incidenceGraph q).mem_edgeSet.mpr (incidence_index_adj p q i)⟩
  have hs : Function.Surjective edge := by
    intro e
    rcases e with ⟨e, he⟩
    revert he
    refine Sym2.inductionOn e (fun u v => ?_)
    intro he
    have hadj := (p.incidenceGraph q).mem_edgeSet.mp he
    cases u with
    | inl s =>
      cases v with
      | inl _ => exact False.elim hadj
      | inr t =>
        obtain ⟨i, hi, hj⟩ := hadj
        refine ⟨i, Subtype.ext ?_⟩
        change s(Sum.inl (p.blockOf i), Sum.inr (q.blockOf i)) = s(Sum.inl s, Sum.inr t)
        rw [blockOf_eq_of_mem p s hi, blockOf_eq_of_mem q t hj]
    | inr t =>
      cases v with
      | inr _ => exact False.elim hadj
      | inl s =>
        obtain ⟨i, hi, hj⟩ := hadj
        refine ⟨i, Subtype.ext ?_⟩
        change s(Sum.inl (p.blockOf i), Sum.inr (q.blockOf i)) = s(Sum.inr t, Sum.inl s)
        rw [blockOf_eq_of_mem p s hi, blockOf_eq_of_mem q t hj]
        exact Sym2.eq_swap
  simpa using Nat.card_le_card_of_surjective edge hs

/-- Two raw-join-connected partitions have at most `n+1` blocks in total.
No noncrossing compatibility, acyclicity, or complement assumption is used. -/
theorem card_blocks_add_le_of_sup_val_eq_top (p q : NoncrossingPartition n)
    (hn : 0 < n) (hjoin : p.val ⊔ q.val = ⊤) :
    p.blocks.card + q.blocks.card ≤ n + 1 := by
  have hc := (p.incidenceGraph_connected_of_sup_val_eq_top q hn hjoin).card_vert_le_card_edgeSet_add_one
  have he := p.incidenceGraph_card_edges_le q
  have hv : Nat.card (IncidenceVertices p q) = p.blocks.card + q.blocks.card := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_coe]
  rw [hv] at hc
  omega

end FreeProbability.NoncrossingPartition

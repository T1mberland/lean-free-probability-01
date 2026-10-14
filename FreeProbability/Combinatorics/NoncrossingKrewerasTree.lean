import FreeProbability.Combinatorics.NoncrossingKrewerasCardinality
import FreeProbability.Combinatorics.NoncrossingIncidenceGraph
import FreeProbability.Combinatorics.NoncrossingInterleaveJoin

/-! # The actual Kreweras block-incidence tree -/

namespace FreeProbability.NoncrossingPartition

variable {n : ℕ}

/-- Every nonempty partition and its constructed complement have a genuinely
connected block-incidence graph. -/
theorem incidenceGraph_kreweras_connected (p : NoncrossingPartition n) (hn : 0 < n) :
    (p.incidenceGraph p.kreweras).Connected :=
  p.incidenceGraph_connected_of_sup_val_eq_top p.kreweras hn p.sup_kreweras_val_eq_top

/-- All original indices produce distinct actual complementary incidence edges. -/
theorem incidenceGraph_kreweras_card_edges (p : NoncrossingPartition n) (hn : 0 < n) :
    Nat.card (p.incidenceGraph p.kreweras).edgeSet = n := by
  have hv : Nat.card (IncidenceVertices p p.kreweras) = n + 1 := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_coe]
    exact p.card_blocks_add_kreweras hn
  have hc := (p.incidenceGraph_kreweras_connected hn).card_vert_le_card_edgeSet_add_one
  have he := p.incidenceGraph_card_edges_le p.kreweras
  rw [hv] at hc
  omega

/-- The bipartite graph on the actual blocks of a nonempty noncrossing partition
and its actual Kreweras complement is a tree, with no graph assumptions. -/
theorem incidenceGraph_kreweras_isTree (p : NoncrossingPartition n) (hn : 0 < n) :
    (p.incidenceGraph p.kreweras).IsTree := by
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨p.incidenceGraph_kreweras_connected hn, ?_⟩
  rw [p.incidenceGraph_kreweras_card_edges hn]
  simp only [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_coe]
  exact (p.card_blocks_add_kreweras hn).symm

end FreeProbability.NoncrossingPartition

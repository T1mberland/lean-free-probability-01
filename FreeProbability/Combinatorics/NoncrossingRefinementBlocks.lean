import FreeProbability.Combinatorics.NoncrossingRefinementEquiv
import FreeProbability.Combinatorics.BlockWordTransport

/-! # Actual block families and contribution products for simultaneous refinement -/

namespace FreeProbability.NoncrossingPartition

variable {n : ℕ}

/-- Local relations agree with global relations on the parent-block enumeration. -/
theorem refineBlocks_rel_orderEmb (p : NoncrossingPartition n) (R : BlockRefinements p)
    (s : {s // s ∈ p.blocks}) (a b : Fin s.val.card) :
    (p.refineBlocks R).val.r (s.val.orderEmbOfFin rfl a) (s.val.orderEmbOfFin rfl b) ↔ (R s).val.r a b := by
  exact (congrArg (fun q : NoncrossingPartition s.val.card => q.val.r a b)
    (p.restrict_refineBlocks R s)).to_iff

/-- Each local block lifts to an actual block of the simultaneous refinement. -/
theorem local_block_mem_refineBlocks (p : NoncrossingPartition n) (R : BlockRefinements p)
    (s : {s // s ∈ p.blocks}) {t : Finset (Fin s.val.card)} (ht : t ∈ (R s).blocks) :
    t.image (s.val.orderEmbOfFin rfl) ∈ (p.refineBlocks R).blocks := by
  classical
  obtain ⟨a, ha⟩ := (R s).block_nonempty ht
  obtain ⟨u, ⟨hu, hau⟩, _⟩ := (p.refineBlocks R).existsUnique_block (s.val.orderEmbOfFin rfl a)
  have he : u = t.image (s.val.orderEmbOfFin rfl) := by
    ext b
    by_cases hb : b ∈ s.val
    · have hr : b ∈ Set.range (s.val.orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]
        exact hb
      obtain ⟨k, rfl⟩ := hr
      rw [← (p.refineBlocks R).rel_iff_mem_block hu hau _, p.refineBlocks_rel_orderEmb R s a k,
        (R s).rel_iff_mem_block ht ha k]
      constructor
      · intro h
        exact Finset.mem_image.mpr ⟨k, h, rfl⟩
      · intro h
        obtain ⟨j, hj, he⟩ := Finset.mem_image.mp h
        exact (s.val.orderEmbOfFin rfl).injective he ▸ hj
    · have hbu : b ∉ u := by
        intro h
        have hrel := (p.refineBlocks_le R)
          (((p.refineBlocks R).rel_iff_mem_block hu hau b).mpr h)
        exact hb ((p.rel_iff_mem_block s.property (s.val.orderEmbOfFin_mem rfl a) b).mp hrel)
      have hbi : b ∉ t.image (s.val.orderEmbOfFin rfl) := by
        intro h
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp h
        exact hb (s.val.orderEmbOfFin_mem rfl j)
      simp [hbu, hbi]
  exact he ▸ hu

/-- All refined blocks are exactly the union of the lifted local blocks. -/
theorem blocks_refineBlocks (p : NoncrossingPartition n) (R : BlockRefinements p) :
    (p.refineBlocks R).blocks = p.blocks.attach.biUnion
      (fun s => (R s).blocks.image (fun t => t.image (s.val.orderEmbOfFin rfl))) := by
  classical
  ext u
  rw [Finset.mem_biUnion]
  constructor
  · intro hu
    obtain ⟨a, hau⟩ := (p.refineBlocks R).block_nonempty hu
    obtain ⟨s, ⟨hs, has⟩, _⟩ := p.existsUnique_block a
    let b : {s // s ∈ p.blocks} := ⟨s, hs⟩
    have hr : a ∈ Set.range (s.orderEmbOfFin rfl) := by rw [Finset.range_orderEmbOfFin]; exact has
    obtain ⟨k, rfl⟩ := hr
    obtain ⟨t, ⟨ht, hkt⟩, _⟩ := (R b).existsUnique_block k
    have hi : s.orderEmbOfFin rfl k ∈ t.image (s.orderEmbOfFin rfl) := Finset.mem_image.mpr ⟨k, hkt, rfl⟩
    have he : t.image (s.orderEmbOfFin rfl) = u :=
      ((p.refineBlocks R).existsUnique_block (s.orderEmbOfFin rfl k)).unique
        ⟨p.local_block_mem_refineBlocks R b ht, hi⟩ ⟨hu, hau⟩
    exact ⟨b, Finset.mem_attach _ _, Finset.mem_image.mpr ⟨t, ht, he⟩⟩
  · rintro ⟨s, _, hu⟩
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
    exact p.local_block_mem_refineBlocks R s ht

/-- Lifted block families from distinct parent blocks are disjoint. -/
theorem pairwiseDisjoint_refineBlocks (p : NoncrossingPartition n) (R : BlockRefinements p) :
    Set.PairwiseDisjoint (↑p.blocks.attach)
      (fun s => (R s).blocks.image (fun t => t.image (s.val.orderEmbOfFin rfl))) := by
  classical
  intro s _ t _ hst
  apply Finset.disjoint_left.mpr
  intro u hus hut
  obtain ⟨v, hv, huv⟩ := Finset.mem_image.mp hus
  obtain ⟨w, hw, huw⟩ := Finset.mem_image.mp hut
  obtain ⟨a, ha⟩ := (R s).block_nonempty hv
  have hai : s.val.orderEmbOfFin rfl a ∈ u := huv ▸ Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have hat : s.val.orderEmbOfFin rfl a ∈ t.val := by
    rw [← huw] at hai
    obtain ⟨b, _, he⟩ := Finset.mem_image.mp hai
    exact he ▸ t.val.orderEmbOfFin_mem rfl b
  exact hst (Subtype.ext ((p.existsUnique_block (s.val.orderEmbOfFin rfl a)).unique
    ⟨s.property, s.val.orderEmbOfFin_mem rfl a⟩ ⟨t.property, hat⟩))

end FreeProbability.NoncrossingPartition

namespace FreeProbability

variable {n : ℕ} {X 𝕜 : Type*} [CommMonoid 𝕜]

/-- A simultaneous refinement contribution is the product of its independent local contributions. -/
theorem orderedPartitionContribution_refineBlocks (K : List X → 𝕜) (x : Fin n → X)
    (p : NoncrossingPartition n) (R : p.BlockRefinements) :
    orderedPartitionContribution K x (p.refineBlocks R) =
      ∏ s ∈ p.blocks.attach, orderedPartitionContribution K (x ∘ s.val.orderEmbOfFin rfl) (R s) := by
  classical
  unfold orderedPartitionContribution
  rw [p.blocks_refineBlocks, Finset.prod_biUnion (p.pairwiseDisjoint_refineBlocks R)]
  apply Finset.prod_congr rfl
  intro s _
  rw [Finset.prod_image]
  · apply Finset.prod_congr rfl
    intro t _
    exact congrArg K (orderedBlockWord_image x (s.val.orderEmbOfFin rfl) t)
  · exact fun _ _ _ _ h => Finset.image_injective (s.val.orderEmbOfFin rfl).injective h

end FreeProbability

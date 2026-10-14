import FreeProbability.Combinatorics.NoncrossingBlockRefinement
import FreeProbability.Combinatorics.BlockWordTransport

/-! # Actual blocks and contributions of a single-block refinement -/

namespace FreeProbability.NoncrossingPartition

variable {n : ℕ}

/-- Distinct actual blocks have no common position. -/
theorem not_mem_block_of_mem_other (p : NoncrossingPartition n)
    {s t : Finset (Fin n)} (hs : s ∈ p.blocks) (ht : t ∈ p.blocks) (hst : s ≠ t)
    {a : Fin n} (ha : a ∈ t) : a ∉ s := by
  intro has
  exact hst ((p.existsUnique_block a).unique ⟨hs, has⟩ ⟨ht, ha⟩)

/-- All original blocks other than the replaced block persist unchanged. -/
theorem old_block_mem_refineBlock (p : NoncrossingPartition n) (s : Finset (Fin n))
    (hs : s ∈ p.blocks) (r : NoncrossingPartition s.card)
    {t : Finset (Fin n)} (ht : t ∈ p.blocks) (hts : t ≠ s) :
    t ∈ (p.refineBlock s hs r).blocks := by
  classical
  obtain ⟨a, ha⟩ := p.block_nonempty ht
  have has : a ∉ s := p.not_mem_block_of_mem_other hs ht hts.symm ha
  obtain ⟨u, ⟨hu, hau⟩, _⟩ := (p.refineBlock s hs r).existsUnique_block a
  have he : u = t := by
    ext b
    rw [← (p.refineBlock s hs r).rel_iff_mem_block hu hau b,
      p.refineBlock_rel_of_not_mem s hs r a b has, p.rel_iff_mem_block ht ha b]
  exact he ▸ hu

/-- Ordered enumeration sees exactly the chosen local partition relation. -/
theorem refineBlock_rel_orderEmb (p : NoncrossingPartition n) (s : Finset (Fin n))
    (hs : s ∈ p.blocks) (r : NoncrossingPartition s.card) (a b : Fin s.card) :
    (p.refineBlock s hs r).val.r (s.orderEmbOfFin rfl a) (s.orderEmbOfFin rfl b) ↔ r.val.r a b := by
  have he := congrArg (fun q : NoncrossingPartition s.card => q.val.r a b)
    (p.restrict_refineBlock s hs r)
  exact he.to_iff

/-- Every local block becomes its ordered image in the global refinement. -/
theorem local_block_mem_refineBlock (p : NoncrossingPartition n) (s : Finset (Fin n))
    (hs : s ∈ p.blocks) (r : NoncrossingPartition s.card)
    {t : Finset (Fin s.card)} (ht : t ∈ r.blocks) :
    t.image (s.orderEmbOfFin rfl) ∈ (p.refineBlock s hs r).blocks := by
  classical
  obtain ⟨a, ha⟩ := r.block_nonempty ht
  obtain ⟨u, ⟨hu, hau⟩, _⟩ := (p.refineBlock s hs r).existsUnique_block (s.orderEmbOfFin rfl a)
  have he : u = t.image (s.orderEmbOfFin rfl) := by
    ext b
    by_cases hb : b ∈ s
    · have hr : b ∈ Set.range (s.orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]
        exact hb
      obtain ⟨k, rfl⟩ := hr
      rw [← (p.refineBlock s hs r).rel_iff_mem_block hu hau _,
        p.refineBlock_rel_orderEmb s hs r a k, r.rel_iff_mem_block ht ha k]
      constructor
      · intro h
        exact Finset.mem_image.mpr ⟨k, h, rfl⟩
      · intro h
        obtain ⟨j, hj, he⟩ := Finset.mem_image.mp h
        exact (s.orderEmbOfFin rfl).injective he ▸ hj
    · have hbu : b ∉ u := by
        intro h
        have hrel := (p.refineBlock_le s hs r)
          (((p.refineBlock s hs r).rel_iff_mem_block hu hau b).mpr h)
        exact hb ((p.rel_iff_mem_block hs (s.orderEmbOfFin_mem rfl a) b).mp hrel)
      have hbi : b ∉ t.image (s.orderEmbOfFin rfl) := by
        intro h
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp h
        exact hb (s.orderEmbOfFin_mem rfl j)
      simp [hbu, hbi]
  exact he ▸ hu

/-- The complete block decomposition of a single-block refinement. -/
theorem blocks_refineBlock (p : NoncrossingPartition n) (s : Finset (Fin n))
    (hs : s ∈ p.blocks) (r : NoncrossingPartition s.card) :
    (p.refineBlock s hs r).blocks = p.blocks.erase s ∪
      r.blocks.image (fun t => t.image (s.orderEmbOfFin rfl)) := by
  classical
  ext u
  rw [Finset.mem_union, Finset.mem_image]
  constructor
  · intro hu
    obtain ⟨a, hau⟩ := (p.refineBlock s hs r).block_nonempty hu
    by_cases ha : a ∈ s
    · have hr : a ∈ Set.range (s.orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]
        exact ha
      obtain ⟨k, rfl⟩ := hr
      obtain ⟨t, ⟨ht, hkt⟩, _⟩ := r.existsUnique_block k
      have hi : s.orderEmbOfFin rfl k ∈ t.image (s.orderEmbOfFin rfl) :=
        Finset.mem_image.mpr ⟨k, hkt, rfl⟩
      have he := ((p.refineBlock s hs r).existsUnique_block (s.orderEmbOfFin rfl k)).unique
        ⟨p.local_block_mem_refineBlock s hs r ht, hi⟩ ⟨hu, hau⟩
      exact Or.inr ⟨t, ht, he⟩
    · obtain ⟨t, ⟨ht, hat⟩, _⟩ := p.existsUnique_block a
      have hts : t ≠ s := fun he => ha (he ▸ hat)
      have he : u = t := ((p.refineBlock s hs r).existsUnique_block a).unique
        ⟨hu, hau⟩ ⟨p.old_block_mem_refineBlock s hs r ht hts, hat⟩
      exact Or.inl (he.symm ▸ Finset.mem_erase.mpr ⟨hts, ht⟩)
  · rintro (hu | ⟨t, ht, rfl⟩)
    · obtain ⟨hus, hu⟩ := Finset.mem_erase.mp hu
      exact p.old_block_mem_refineBlock s hs r hu hus
    · exact p.local_block_mem_refineBlock s hs r ht

end FreeProbability.NoncrossingPartition

namespace FreeProbability

variable {n : ℕ} {X 𝕜 : Type*} [CommMonoid 𝕜]

/-- Refining one block factors its contribution into the unchanged outside product
and the local partition contribution. -/
theorem orderedPartitionContribution_refineBlock (K : List X → 𝕜) (x : Fin n → X)
    (p : NoncrossingPartition n) (s : Finset (Fin n)) (hs : s ∈ p.blocks)
    (r : NoncrossingPartition s.card) :
    orderedPartitionContribution K x (p.refineBlock s hs r) =
      (∏ t ∈ p.blocks.erase s, K (orderedBlockWord x t)) *
        orderedPartitionContribution K (x ∘ s.orderEmbOfFin rfl) r := by
  classical
  unfold orderedPartitionContribution
  rw [p.blocks_refineBlock s hs r]
  have hd : Disjoint (p.blocks.erase s)
      (r.blocks.image (fun t => t.image (s.orderEmbOfFin rfl))) := by
    apply Finset.disjoint_left.mpr
    intro t ht hti
    obtain ⟨hts, ht⟩ := Finset.mem_erase.mp ht
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hti
    obtain ⟨a, ha⟩ := r.block_nonempty hu
    have hai : s.orderEmbOfFin rfl a ∈ u.image (s.orderEmbOfFin rfl) :=
      Finset.mem_image.mpr ⟨a, ha, rfl⟩
    exact p.not_mem_block_of_mem_other hs ht hts.symm hai (s.orderEmbOfFin_mem rfl a)
  rw [Finset.prod_union hd, Finset.prod_image]
  · congr 1
    apply Finset.prod_congr rfl
    intro t _
    exact congrArg K (orderedBlockWord_image x (s.orderEmbOfFin rfl) t)
  · intro a _ b _ h
    exact Finset.image_injective (s.orderEmbOfFin rfl).injective h

end FreeProbability

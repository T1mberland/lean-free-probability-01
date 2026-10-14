import FreeProbability.Combinatorics.NoncrossingInterleave
import FreeProbability.Combinatorics.BlockWordTransport

/-! # Exact block and contribution factorization for Kreweras interleavings -/

namespace FreeProbability.NoncrossingPartition

variable {n : ℕ}

/-- Original blocks become actual blocks on original positions. -/
theorem image_odd_mem_blocks_interleave (p q : NoncrossingPartition n) (hq : q ≤ p.kreweras)
    {s : Finset (Fin n)} (hs : s ∈ p.blocks) :
    s.image oddOrderEmbedding ∈ (p.interleave q hq).blocks := by
  classical
  obtain ⟨i, hi⟩ := p.block_nonempty hs
  obtain ⟨t, ⟨ht, hit⟩, _⟩ := (p.interleave q hq).existsUnique_block (oddPosition i)
  have he : t = s.image oddOrderEmbedding := by
    ext a
    rw [← (p.interleave q hq).rel_iff_mem_block ht hit a]
    rcases position_cases a with ha | ha
    · rw [ha]
      change (interleaveSetoid p q).r (oddPosition i) (oddPosition (halfPosition a)) ↔ _
      rw [interleave_odd_odd, p.rel_iff_mem_block hs hi]
      change halfPosition a ∈ s ↔ oddOrderEmbedding (halfPosition a) ∈ s.image oddOrderEmbedding
      simp only [Finset.mem_image, oddOrderEmbedding.injective.eq_iff, exists_eq_right]
    · rw [ha]
      have hn : evenPosition (halfPosition a) ∉ s.image oddOrderEmbedding := by
        intro h
        obtain ⟨b, _, hb⟩ := Finset.mem_image.mp h
        have hv := congrArg Fin.val hb
        change 2 * b.val = 2 * (halfPosition a).val + 1 at hv
        omega
      simp only [hn, iff_false]
      exact interleave_odd_even p q _ _
  exact he ▸ ht

/-- Complementary blocks become actual blocks on complementary positions. -/
theorem image_even_mem_blocks_interleave (p q : NoncrossingPartition n) (hq : q ≤ p.kreweras)
    {s : Finset (Fin n)} (hs : s ∈ q.blocks) :
    s.image evenOrderEmbedding ∈ (p.interleave q hq).blocks := by
  classical
  obtain ⟨i, hi⟩ := q.block_nonempty hs
  obtain ⟨t, ⟨ht, hit⟩, _⟩ := (p.interleave q hq).existsUnique_block (evenPosition i)
  have he : t = s.image evenOrderEmbedding := by
    ext a
    rw [← (p.interleave q hq).rel_iff_mem_block ht hit a]
    rcases position_cases a with ha | ha
    · rw [ha]
      have hn : oddPosition (halfPosition a) ∉ s.image evenOrderEmbedding := by
        intro h
        obtain ⟨b, _, hb⟩ := Finset.mem_image.mp h
        have hv := congrArg Fin.val hb
        change 2 * b.val + 1 = 2 * (halfPosition a).val at hv
        omega
      constructor
      · intro h
        exact False.elim (interleave_odd_even p q _ _ ((interleaveSetoid p q).symm h))
      · exact fun h => False.elim (hn h)
    · rw [ha]
      change (interleaveSetoid p q).r (evenPosition i) (evenPosition (halfPosition a)) ↔ _
      rw [interleave_even_even, q.rel_iff_mem_block hs hi]
      change halfPosition a ∈ s ↔ evenOrderEmbedding (halfPosition a) ∈ s.image evenOrderEmbedding
      simp only [Finset.mem_image, evenOrderEmbedding.injective.eq_iff, exists_eq_right]
  exact he ▸ ht

/-- The block family of the interleaving is exactly the disjoint parity images. -/
theorem blocks_interleave (p q : NoncrossingPartition n) (hq : q ≤ p.kreweras) :
    (p.interleave q hq).blocks =
      p.blocks.image (fun s => s.image oddOrderEmbedding) ∪
        q.blocks.image (fun s => s.image evenOrderEmbedding) := by
  classical
  ext t
  rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
  constructor
  · intro ht
    obtain ⟨a, hat⟩ := (p.interleave q hq).block_nonempty ht
    rcases position_cases a with ha | ha
    · obtain ⟨s, ⟨hs, has⟩, _⟩ := p.existsUnique_block (halfPosition a)
      have hsa : a ∈ s.image oddOrderEmbedding := Finset.mem_image.mpr ⟨_, has, ha.symm⟩
      left
      exact ⟨s, hs, ((p.interleave q hq).existsUnique_block a).unique
        ⟨p.image_odd_mem_blocks_interleave q hq hs, hsa⟩ ⟨ht, hat⟩⟩
    · obtain ⟨s, ⟨hs, has⟩, _⟩ := q.existsUnique_block (halfPosition a)
      have hsa : a ∈ s.image evenOrderEmbedding := Finset.mem_image.mpr ⟨_, has, ha.symm⟩
      right
      exact ⟨s, hs, ((p.interleave q hq).existsUnique_block a).unique
        ⟨p.image_even_mem_blocks_interleave q hq hs, hsa⟩ ⟨ht, hat⟩⟩
  · rintro (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
    · exact p.image_odd_mem_blocks_interleave q hq hs
    · exact p.image_even_mem_blocks_interleave q hq hs

/-- The two parity block families cannot share a nonempty block. -/
theorem interleave_block_images_disjoint (p q : NoncrossingPartition n) :
    Disjoint (p.blocks.image (fun s => s.image oddOrderEmbedding))
      (q.blocks.image (fun s => s.image evenOrderEmbedding)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro s hs ht
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨v, _, he⟩ := Finset.mem_image.mp ht
  obtain ⟨a, ha⟩ := p.block_nonempty hu
  have hm : oddPosition a ∈ v.image evenOrderEmbedding := he.symm ▸ Finset.mem_image.mpr ⟨a, ha, rfl⟩
  obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hm
  have hv := congrArg Fin.val hb
  change 2 * b.val + 1 = 2 * a.val at hv
  omega

end FreeProbability.NoncrossingPartition

namespace FreeProbability

variable {n : ℕ} {X 𝕜 : Type*} [CommMonoid 𝕜]

/-- Every ordered partition contribution factors into the original and
complementary contributions, with their precise sorted word restrictions. -/
theorem orderedPartitionContribution_interleave (K : List X → 𝕜) (x : Fin (2 * n) → X)
    (p q : NoncrossingPartition n) (hq : q ≤ p.kreweras) :
    orderedPartitionContribution K x (p.interleave q hq) =
      orderedPartitionContribution K (x ∘ NoncrossingPartition.oddOrderEmbedding) p *
        orderedPartitionContribution K (x ∘ NoncrossingPartition.evenOrderEmbedding) q := by
  classical
  unfold orderedPartitionContribution
  rw [p.blocks_interleave q hq, Finset.prod_union (p.interleave_block_images_disjoint q)]
  congr 1
  · rw [Finset.prod_image]
    · apply Finset.prod_congr rfl
      intro s _
      exact congrArg K (orderedBlockWord_image x NoncrossingPartition.oddOrderEmbedding s)
    · exact fun _ _ _ _ h => Finset.image_injective NoncrossingPartition.oddOrderEmbedding.injective h
  · rw [Finset.prod_image]
    · apply Finset.prod_congr rfl
      intro s _
      exact congrArg K (orderedBlockWord_image x NoncrossingPartition.evenOrderEmbedding s)
    · exact fun _ _ _ _ h => Finset.image_injective NoncrossingPartition.evenOrderEmbedding.injective h

end FreeProbability

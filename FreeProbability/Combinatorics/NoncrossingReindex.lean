import FreeProbability.Combinatorics.NoncrossingRestriction
import FreeProbability.Combinatorics.BlockWordTransport

/-! # Order-isomorphism reindexing of noncrossing partitions and contributions -/

namespace FreeProbability.NoncrossingPartition

variable {m n : ℕ}

/-- Order-isomorphisms induce equivalences on noncrossing partitions. -/
def reindexEquiv (e : Fin m ≃o Fin n) : NoncrossingPartition n ≃ NoncrossingPartition m where
  toFun p := p.restrict e.toOrderEmbedding
  invFun p := p.restrict e.symm.toOrderEmbedding
  left_inv p := by
    apply Subtype.ext
    apply Setoid.ext
    intro a b
    change p.val.r (e (e.symm a)) (e (e.symm b)) ↔ p.val.r a b
    simp
  right_inv p := by
    apply Subtype.ext
    apply Setoid.ext
    intro a b
    change p.val.r (e.symm (e a)) (e.symm (e b)) ↔ p.val.r a b
    simp

/-- Bijective reindexing retains every block. -/
theorem blocks_reindex (p : NoncrossingPartition n) (e : Fin m ≃o Fin n) :
    (p.restrict e.toOrderEmbedding).blocks = p.blocks.image (pullbackBlock e.toOrderEmbedding) := by
  classical
  rw [blocks_restrict]
  congr 1
  apply Finset.filter_eq_self.mpr
  intro s hs
  obtain ⟨a, ha⟩ := p.block_nonempty hs
  exact ⟨e.symm a, (mem_pullbackBlock _ _ _).mpr (by simpa using ha)⟩

/-- Distinct original blocks remain distinct after bijective reindexing. -/
theorem pullbackBlock_injective (e : Fin m ≃o Fin n) :
    Function.Injective (pullbackBlock e.toOrderEmbedding) := by
  intro s t h
  have he := congrArg (fun u => u.image e.toOrderEmbedding) h
  rw [image_pullbackBlock e.toOrderEmbedding s (fun a _ => e.surjective a),
    image_pullbackBlock e.toOrderEmbedding t (fun a _ => e.surjective a)] at he
  exact he

end FreeProbability.NoncrossingPartition

namespace FreeProbability

variable {m n : ℕ} {X 𝕜 : Type*} [CommMonoid 𝕜]

/-- Ordered partition contributions are invariant under order-isomorphism reindexing. -/
theorem orderedPartitionContribution_reindex (K : List X → 𝕜) (x : Fin n → X)
    (p : NoncrossingPartition n) (e : Fin m ≃o Fin n) :
    orderedPartitionContribution K (x ∘ e) (p.restrict e.toOrderEmbedding) =
      orderedPartitionContribution K x p := by
  classical
  unfold orderedPartitionContribution
  rw [p.blocks_reindex, Finset.prod_image]
  · apply Finset.prod_congr rfl
    intro s _
    apply congrArg K
    have hw := orderedBlockWord_image x e.toOrderEmbedding
      (NoncrossingPartition.pullbackBlock e.toOrderEmbedding s)
    rw [NoncrossingPartition.image_pullbackBlock e.toOrderEmbedding s (fun a _ => e.surjective a)] at hw
    exact hw.symm
  · exact fun _ _ _ _ h => NoncrossingPartition.pullbackBlock_injective e h

end FreeProbability

namespace FreeProbability

variable {m n : ℕ}

/-- Noncrossing partitions whose every block meets one of two specified positions. -/
abbrev PointCoveringPartitions (u v : Fin n) :=
  {p : NoncrossingPartition n // ∀ a, p.val.r a u ∨ p.val.r a v}

noncomputable instance (u v : Fin n) : Fintype (PointCoveringPartitions u v) := Fintype.ofFinite _

/-- Reindexing transports the marked-point covering condition as well. -/
def pointCoveringReindexEquiv (e : Fin m ≃o Fin n) (u v : Fin n) :
    PointCoveringPartitions u v ≃ PointCoveringPartitions (e.symm u) (e.symm v) where
  toFun p := ⟨NoncrossingPartition.reindexEquiv e p.val, by
    intro a
    change p.val.val.r (e a) (e (e.symm u)) ∨ p.val.val.r (e a) (e (e.symm v))
    simpa only [e.apply_symm_apply] using p.property (e a)⟩
  invFun p := ⟨(NoncrossingPartition.reindexEquiv e).symm p.val, by
    intro a
    change p.val.val.r (e.symm a) (e.symm u) ∨ p.val.val.r (e.symm a) (e.symm v)
    exact p.property (e.symm a)⟩
  left_inv p := Subtype.ext ((NoncrossingPartition.reindexEquiv e).symm_apply_apply p.val)
  right_inv p := Subtype.ext ((NoncrossingPartition.reindexEquiv e).apply_symm_apply p.val)

/-- Marked covering sums are invariant under an order-isomorphism of the positions. -/
theorem sum_pointCoveringPartitionContribution_reindex {X 𝕜 : Type*} [CommSemiring 𝕜]
    (K : List X → 𝕜) (x : Fin n → X) (u v : Fin n) (e : Fin m ≃o Fin n) :
    (∑ p : PointCoveringPartitions u v, orderedPartitionContribution K x p.val) =
      ∑ p : PointCoveringPartitions (e.symm u) (e.symm v),
        orderedPartitionContribution K (x ∘ e) p.val := by
  classical
  apply Fintype.sum_equiv (pointCoveringReindexEquiv e u v)
  intro p
  exact (orderedPartitionContribution_reindex K x p.val e).symm

end FreeProbability

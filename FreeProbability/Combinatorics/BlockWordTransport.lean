import FreeProbability.Combinatorics.Cumulant
import FreeProbability.Combinatorics.NoncrossingSingletonInsertion

/-!
# Ordered block words under singleton insertion

The tuple presentation avoids casts between the length of a list and the size
of its index set. Singleton insertion multiplies the partition contribution by
the singleton cumulant and leaves every other block word unchanged.
-/

namespace FreeProbability

variable {X 𝕜 : Type*} {n m : ℕ}

/-- Read the positions of a block in increasing order from a tuple. -/
def orderedBlockWord (x : Fin n → X) (s : Finset (Fin n)) : List X :=
  s.sort.map x

@[simp] theorem orderedBlockWord_get (w : List X) (s : Finset (Fin w.length)) :
    orderedBlockWord w.get s = blockWord w s := rfl

/-- An order embedding transports a block without changing its ordered letters. -/
theorem orderedBlockWord_image (x : Fin m → X) (f : Fin n ↪o Fin m)
    (s : Finset (Fin n)) :
    orderedBlockWord x (s.image f) = orderedBlockWord (x ∘ f) s := by
  classical
  unfold orderedBlockWord
  change ((s.image f.toEmbedding).sort (· ≤ ·)).map x = _
  rw [← Finset.map_eq_image f.toEmbedding s]
  rw [← Finset.map_sort f.toEmbedding s (· ≤ ·) (· ≤ ·)
    (fun _ _ _ _ => f.le_iff_le.symm), List.map_map]
  rfl

/-- Partition contributions written on a tuple rather than on a list. -/
noncomputable def orderedPartitionContribution [CommMonoid 𝕜] (K : List X → 𝕜)
    (x : Fin n → X) (p : NoncrossingPartition n) : 𝕜 :=
  ∏ s ∈ p.blocks, K (orderedBlockWord x s)

@[simp] theorem orderedPartitionContribution_get [Field 𝕜]
    (K : List X → 𝕜) (w : List X) (p : NoncrossingPartition w.length) :
    orderedPartitionContribution K w.get p = partitionContribution K w p := by
  classical
  unfold orderedPartitionContribution partitionContribution
  rw [Finset.prod_attach p.blocks (fun s => K (blockWord w s))]
  rfl

/-- Exact contribution transport under insertion of a singleton position. -/
theorem orderedPartitionContribution_insertSingleton [CommMonoid 𝕜]
    (K : List X → 𝕜) (x : Fin (n + 1) → X) (p : NoncrossingPartition n)
    (i : Fin (n + 1)) :
    orderedPartitionContribution K x (p.insertSingleton i) =
      K [x i] * orderedPartitionContribution K (x ∘ i.succAbove) p := by
  classical
  unfold orderedPartitionContribution
  rw [p.blocks_insertSingleton]
  have hnot : {i} ∉ p.blocks.image (fun s => s.image i.succAbove) := by
    intro h
    obtain ⟨s, _, he⟩ := Finset.mem_image.mp h
    have hi : i ∈ s.image i.succAbove := he.symm ▸ Finset.mem_singleton_self i
    obtain ⟨a, _, hai⟩ := Finset.mem_image.mp hi
    exact i.succAbove_ne a hai
  rw [Finset.prod_insert hnot, Finset.prod_image]
  · simp only [orderedBlockWord, Finset.sort_singleton, List.map_cons, List.map_nil]
    congr 1
    apply Finset.prod_congr rfl
    intro s _
    exact congrArg K (orderedBlockWord_image x i.succAboveOrderEmb s)
  · intro s _ t _ h
    exact Finset.image_injective i.succAbove_right_injective h

/-- Noncrossing partitions with a prescribed singleton position. -/
abbrev SingletonNoncrossingPartition (i : Fin (n + 1)) :=
  {p : NoncrossingPartition (n + 1) // ∀ j, p.val.r i j → j = i}

noncomputable instance (i : Fin (n + 1)) : Fintype (SingletonNoncrossingPartition i) :=
  Fintype.ofFinite _

/-- The entire singleton-containing partition sum factors through the shorter word. -/
theorem sum_orderedPartitionContribution_singleton [CommSemiring 𝕜]
    (K : List X → 𝕜) (x : Fin (n + 1) → X) (i : Fin (n + 1)) :
    (∑ q : SingletonNoncrossingPartition i, orderedPartitionContribution K x q.val) =
      K [x i] * ∑ p : NoncrossingPartition n,
        orderedPartitionContribution K (x ∘ i.succAbove) p := by
  classical
  rw [← (NoncrossingPartition.singletonInsertionEquiv i).sum_comp
    (fun q => orderedPartitionContribution K x q.val)]
  change (∑ p : NoncrossingPartition n,
    orderedPartitionContribution K x (p.insertSingleton i)) = _
  simp only [orderedPartitionContribution_insertSingleton, Finset.mul_sum]

end FreeProbability

import FreeProbability.Combinatorics.Cumulant
import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
# Products of multilinear block functions

Every coordinate belongs to exactly one partition block. Updating that coordinate
changes exactly one factor in the product, so the block product is multilinear.
-/

namespace FreeProbability

open Function

variable {𝕜 A : Type*} [Field 𝕜] [AddCommGroup A] [Module 𝕜 A] {n : ℕ}

/-- A scalar multilinear map for each partition block in its increasing order. -/
abbrev BlockMaps (p : NoncrossingPartition n) :=
  ∀ s : {s // s ∈ p.blocks}, MultilinearMap 𝕜 (fun _ : Fin s.val.card => A) 𝕜

noncomputable def blockProduct (p : NoncrossingPartition n) (K : BlockMaps (𝕜 := 𝕜) (A := A) p)
    (x : Fin n → A) : 𝕜 :=
  ∏ s ∈ p.blocks.attach, K s (x ∘ s.val.orderEmbOfFin rfl)

/-- Updating a coordinate changes only its unique block factor. -/
theorem blockProduct_update (p : NoncrossingPartition n) (K : BlockMaps (𝕜 := 𝕜) (A := A) p)
    (x : Fin n → A) (i : Fin n) (s : {s // s ∈ p.blocks}) (hi : i ∈ s.val)
    (j : Fin s.val.card) (hj : s.val.orderEmbOfFin rfl j = i) (a : A) :
    blockProduct p K (update x i a) =
      K s (update (x ∘ s.val.orderEmbOfFin rfl) j a) *
        ∏ t ∈ p.blocks.attach.erase s, K t (x ∘ t.val.orderEmbOfFin rfl) := by
  classical
  unfold blockProduct
  rw [← Finset.mul_prod_erase p.blocks.attach _ (Finset.mem_attach _ s)]
  have hsel : update x i a ∘ s.val.orderEmbOfFin rfl =
      update (x ∘ s.val.orderEmbOfFin rfl) j a := by
    rw [← hj]
    exact update_comp_eq_of_injective x (s.val.orderEmbOfFin rfl).injective j a
  rw [hsel]
  congr 1
  apply Finset.prod_congr rfl
  intro t ht
  congr 1
  apply update_comp_eq_of_forall_ne
  intro k he
  have hit : i ∈ t.val := he ▸ t.val.orderEmbOfFin_mem rfl k
  obtain ⟨b, hb, huniq⟩ := p.existsUnique_block i
  have hts : t.val = s.val := (huniq _ ⟨t.property, hit⟩).trans (huniq _ ⟨s.property, hi⟩).symm
  exact (Finset.mem_erase.mp ht).1 (Subtype.ext hts)

/-- Assemble block multilinear maps into a multilinear map on the full ordered set. -/
noncomputable def partitionMultilinear (p : NoncrossingPartition n)
    (K : BlockMaps (𝕜 := 𝕜) (A := A) p) : MultilinearMap 𝕜 (fun _ : Fin n => A) 𝕜 := by
  classical
  refine MultilinearMap.mk' (blockProduct p K) ?_ ?_
  · intro x i a b
    obtain ⟨s, ⟨hs, hi⟩, _⟩ := p.existsUnique_block i
    have hir : i ∈ Set.range (s.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact hi
    obtain ⟨j, hj⟩ := hir
    let t : {s // s ∈ p.blocks} := ⟨s, hs⟩
    rw [blockProduct_update p K x i t hi j hj (a + b),
      blockProduct_update p K x i t hi j hj a,
      blockProduct_update p K x i t hi j hj b, (K t).map_update_add, add_mul]
  · intro x i c a
    obtain ⟨s, ⟨hs, hi⟩, _⟩ := p.existsUnique_block i
    have hir : i ∈ Set.range (s.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact hi
    obtain ⟨j, hj⟩ := hir
    let t : {s // s ∈ p.blocks} := ⟨s, hs⟩
    rw [blockProduct_update p K x i t hi j hj (c • a),
      blockProduct_update p K x i t hi j hj a, (K t).map_update_smul]
    simp [smul_eq_mul, mul_assoc]

@[simp] theorem partitionMultilinear_apply (p : NoncrossingPartition n)
    (K : BlockMaps (𝕜 := 𝕜) (A := A) p) (x : Fin n → A) :
    partitionMultilinear p K x = blockProduct p K x := rfl

end FreeProbability

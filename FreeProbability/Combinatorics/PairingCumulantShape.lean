import FreeProbability.Combinatorics.Cumulant
import FreeProbability.Combinatorics.NoncrossingPairing

/-! # The noncrossing moment polynomial of a second-order cumulant shape -/

namespace FreeProbability

variable {X 𝕜 : Type*} [Field 𝕜]

/-- The cumulant family supported exactly at words of length two. -/
def pairingCumulantShape (variance : 𝕜) (w : List X) : 𝕜 :=
  if w.length = 2 then variance else 0

/-- Its full moment polynomial counts noncrossing pairings with the variance weight. -/
theorem sum_partitionContribution_pairingCumulantShape (variance : 𝕜) (w : List X) :
    (∑ p : NoncrossingPartition w.length, partitionContribution (pairingCumulantShape variance) w p) =
      (Fintype.card (NoncrossingPairing w.length) : 𝕜) * variance ^ (w.length / 2) := by
  classical
  have hp (p : NoncrossingPairing w.length) :
      partitionContribution (pairingCumulantShape variance) w p.val = variance ^ (w.length / 2) := by
    unfold partitionContribution
    rw [Finset.prod_attach p.val.blocks (fun s => pairingCumulantShape variance (blockWord w s))]
    have hblock : ∀ s ∈ p.val.blocks, pairingCumulantShape variance (blockWord w s) = variance := by
      intro s hs
      simp [pairingCumulantShape, blockWord_length, p.property s hs]
    calc
      ∏ s ∈ p.val.blocks, pairingCumulantShape variance (blockWord w s) =
        ∏ _s ∈ p.val.blocks, variance := Finset.prod_congr rfl hblock
      _ = variance ^ p.val.blocks.card := by simp
      _ = variance ^ (w.length / 2) := by congr 1; have hn := p.property.card_eq_twice; omega
  have hs : (∑ p : NoncrossingPairing w.length,
      partitionContribution (pairingCumulantShape variance) w p.val) =
      ∑ p : NoncrossingPartition w.length, partitionContribution (pairingCumulantShape variance) w p := by
    apply Fintype.sum_of_injective (fun p : NoncrossingPairing w.length => p.val) Subtype.val_injective
    · intro p hprange
      have hnp : ¬p.IsPairing := fun hp => hprange ⟨⟨p, hp⟩, rfl⟩
      obtain ⟨s, hs⟩ := not_forall.mp hnp
      obtain ⟨hs, hcard⟩ := not_imp.mp hs
      unfold partitionContribution
      apply Finset.prod_eq_zero (i := ⟨s, hs⟩) (Finset.mem_attach _ _)
      simp [pairingCumulantShape, blockWord_length, hcard]
    · intro p
      rfl
  rw [← hs]
  simp [hp, nsmul_eq_mul]

end FreeProbability

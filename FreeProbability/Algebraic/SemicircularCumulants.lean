import FreeProbability.Algebraic.CumulantUnit
import FreeProbability.Combinatorics.NoncrossingPairing

/-!
# Pairing moments from semicircular cumulants

This module proves a conditional algebraic implication: a variable whose only
nonzero cumulant is the second has the noncrossing-pairing moments. It constructs
neither a Fock realization nor a spectral probability measure. No positivity
assumption on the scalar variance is needed for the algebraic implication.
-/

namespace FreeProbability

variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]

/-- Algebraic semicircular cumulants with the prescribed second cumulant. -/
def HasSemicircularCumulants (φ : ProbabilitySpace 𝕜 A) (a : A) (variance : 𝕜) : Prop :=
  ∀ n, cumulant φ (List.replicate n a) = if n = 2 then variance else 0

/-- A variable with semicircular cumulants is centered. -/
theorem HasSemicircularCumulants.centered {φ : ProbabilitySpace 𝕜 A} {a : A} {variance : 𝕜}
    (h : HasSemicircularCumulants φ a variance) : φ.expectation a = 0 := by
  simpa [HasSemicircularCumulants, cumulant, freeCumulant_singleton] using h 1

private theorem semicircular_pairing_contribution {φ : ProbabilitySpace 𝕜 A} {a : A} {variance : 𝕜}
    (h : HasSemicircularCumulants φ a variance) {n : ℕ} (p : NoncrossingPairing n) :
    orderedPartitionContribution (cumulant φ) (fun _ : Fin n => a) p.val = variance ^ (n / 2) := by
  classical
  unfold orderedPartitionContribution
  have hp : ∀ s ∈ p.val.blocks,
      cumulant φ (orderedBlockWord (fun _ : Fin n => a) s) = variance := by
    intro s hs
    simp only [orderedBlockWord, List.map_const', Finset.length_sort]
    rw [h, p.property s hs]
    simp
  calc
    ∏ s ∈ p.val.blocks, cumulant φ (orderedBlockWord (fun _ : Fin n => a) s) =
        ∏ _s ∈ p.val.blocks, variance := Finset.prod_congr rfl hp
    _ = variance ^ p.val.blocks.card := by simp
    _ = variance ^ (n / 2) := by
      congr 1
      have hn := p.property.card_eq_twice
      omega

/-- Every power moment is the sum of noncrossing-pairing weights. -/
theorem HasSemicircularCumulants.expectation_pow {φ : ProbabilitySpace 𝕜 A} {a : A} {variance : 𝕜}
    (h : HasSemicircularCumulants φ a variance) (n : ℕ) :
    φ.expectation (a ^ n) = (Fintype.card (NoncrossingPairing n) : 𝕜) * variance ^ (n / 2) := by
  classical
  have hm := expectation_eq_sum_orderedCumulants φ (fun _ : Fin n => a)
  simp only [List.ofFn_const, List.prod_replicate] at hm
  rw [hm]
  have hs : (∑ p : NoncrossingPairing n,
      orderedPartitionContribution (cumulant φ) (fun _ : Fin n => a) p.val) =
      ∑ p : NoncrossingPartition n,
        orderedPartitionContribution (cumulant φ) (fun _ : Fin n => a) p := by
    apply Fintype.sum_of_injective (fun p : NoncrossingPairing n => p.val) Subtype.val_injective
    · intro p hprange
      have hnp : ¬p.IsPairing := by
        intro hp
        exact hprange ⟨⟨p, hp⟩, rfl⟩
      obtain ⟨s, hs⟩ := not_forall.mp hnp
      obtain ⟨hs, hcard⟩ := not_imp.mp hs
      unfold orderedPartitionContribution
      apply Finset.prod_eq_zero hs
      simp only [orderedBlockWord, List.map_const', Finset.length_sort]
      rw [h]
      simp only [hcard, ite_false]
    · intro p
      rfl
  rw [← hs]
  simp only [semicircular_pairing_contribution h]
  simp [nsmul_eq_mul]

/-- All odd moments vanish. -/
theorem HasSemicircularCumulants.expectation_pow_odd {φ : ProbabilitySpace 𝕜 A} {a : A} {variance : 𝕜}
    (h : HasSemicircularCumulants φ a variance) {n : ℕ} (hn : Odd n) : φ.expectation (a ^ n) = 0 := by
  let : IsEmpty (NoncrossingPairing n) := ⟨fun p => NoncrossingPairing.not_nonempty_of_odd hn ⟨p⟩⟩
  rw [h.expectation_pow]
  simp

/-- At variance one, the moments count the actual noncrossing pairings. -/
theorem HasSemicircularCumulants.expectation_pow_variance_one {φ : ProbabilitySpace 𝕜 A} {a : A}
    (h : HasSemicircularCumulants φ a 1) (n : ℕ) :
    φ.expectation (a ^ n) = (Fintype.card (NoncrossingPairing n) : 𝕜) := by
  rw [h.expectation_pow]
  simp

end FreeProbability

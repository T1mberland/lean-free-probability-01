import FreeProbability.RandomMatrix.OrthogonalPermutationNetwork

/-! # Genuine orbit counts for finite permutations without fixed sites -/

noncomputable section
open scoped Classical
namespace FreeProbability.Orthogonal
open Equiv.Perm
variable {α : Type*} [Fintype α] (σ : Equiv.Perm α)

/-- Every actual orbit contains at least two distinct sites when the genuine
permutation has no fixed sites. ALL singleton orbits are considered. -/
theorem permutationOrbit_length_ge_two (hσ : ∀ a, σ a ≠ a) (c : PermutationOrbitIndex σ) :
    2 ≤ (permutationOrbitFinset σ c).card := by
  have hmem : ∀ b, b = c.out ∨ b = σ c.out → b ∈ permutationOrbitFinset σ c := by
    intro b hb
    simp only [permutationOrbitFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hb with rfl | rfl
    · exact SameCycle.refl _ _
    · exact ⟨1, rfl⟩
  have hsub : {c.out, σ c.out} ⊆ permutationOrbitFinset σ c := by
    intro b hb
    exact hmem b (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hb)
  have hc := Finset.card_le_card hsub
  simpa only [Finset.card_pair (hσ c.out).symm] using hc

/-- An actual finite permutation with no fixed sites has at most half as many
ALL product orbits as sites. Includes empty types, without discarding cycles. -/
theorem twice_permutationOrbit_card_le (hσ : ∀ a, σ a ≠ a) :
    2 * Fintype.card (PermutationOrbitIndex σ) ≤ Fintype.card α := by
  calc
    _ = ∑ _c : PermutationOrbitIndex σ, 2 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact Nat.mul_comm _ _
    _ ≤ ∑ c : PermutationOrbitIndex σ, Fintype.card (PermutationOrbit σ c) := by
      apply Finset.sum_le_sum
      intro c _
      rw [permutationOrbit_card]
      exact permutationOrbit_length_ge_two σ hσ c
    _ = Fintype.card (Σ c : PermutationOrbitIndex σ, PermutationOrbit σ c) :=
      Fintype.card_sigma.symm
    _ = Fintype.card α := Fintype.card_congr (permutationOrbitSigmaEquiv σ)

end FreeProbability.Orthogonal

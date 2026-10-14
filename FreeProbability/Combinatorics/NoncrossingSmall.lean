import FreeProbability.Combinatorics.NoncrossingPartition

/-! # Discrete blocks and the partitions of two positions -/

namespace FreeProbability.NoncrossingPartition

variable {n : ℕ}

/-- The discrete partition consists exactly of singleton blocks. -/
theorem blocks_discrete (n : ℕ) :
    (discrete n).blocks = (Finset.univ : Finset (Fin n)).image (fun i => {i}) := by
  classical
  change (Finset.univ : Finset (Fin n)).image (fun a =>
    {b ∈ (Finset.univ : Finset (Fin n)) | (⊥ : Setoid (Fin n)).r a b}) = _
  congr 1
  funext a
  ext b
  simp [eq_comm]

/-- There are exactly the discrete and indiscrete possibilities at two positions. -/
theorem two_eq_discrete_or_indiscrete (p : NoncrossingPartition 2) :
    p = discrete 2 ∨ p = indiscrete 2 := by
  by_cases hp : p = indiscrete 2
  · exact Or.inr hp
  · left
    apply Subtype.ext
    apply Setoid.ext
    intro a b
    constructor
    · intro hab
      obtain ⟨s, hs, has, hbs⟩ := (p.same_block_iff a b).mpr hab
      have hc : s.card ≤ 1 := by have hlt := p.block_card_lt_of_ne_indiscrete hp hs; omega
      exact (Finset.card_le_one.mp hc) a has b hbs
    · intro hab
      have he : a = b := hab
      exact he ▸ p.val.refl a

/-- The discrete and indiscrete partitions are distinct on two positions. -/
theorem discrete_two_ne_indiscrete : discrete 2 ≠ indiscrete 2 := by
  intro he
  have hr : (discrete 2).val.r (0 : Fin 2) (1 : Fin 2) := by rw [he]; trivial
  have hv := congrArg Fin.val hr
  simp at hv

end FreeProbability.NoncrossingPartition

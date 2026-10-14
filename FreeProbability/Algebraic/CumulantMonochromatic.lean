import FreeProbability.Algebraic.CumulantCharacterization

/-! # Vanishing of partition contributions with mixed blocks -/

namespace FreeProbability

variable {𝕜 A I : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]

/-- Any mixed block kills the entire noncrossing cumulant contribution of a
word from freely independent subalgebras. -/
theorem FreelyIndependent.orderedContribution_eq_zero_of_mixed {φ : ProbabilitySpace 𝕜 A}
    {B : I → Subalgebra 𝕜 A} (hfree : FreelyIndependent φ B) {n : ℕ}
    (x : Fin n → A) (color : Fin n → I) (hmem : ∀ a, x a ∈ B (color a))
    (p : NoncrossingPartition n) (hmixed : ∃ a b, p.val.r a b ∧ color a ≠ color b) :
    orderedPartitionContribution (cumulant φ) x p = 0 := by
  classical
  obtain ⟨a, b, hab, hneq⟩ := hmixed
  obtain ⟨s, hs, has, hbs⟩ := (p.same_block_iff a b).mpr hab
  let j := (s.orderIsoOfFin rfl).symm ⟨a, has⟩
  let k := (s.orderIsoOfFin rfl).symm ⟨b, hbs⟩
  have hj : s.orderEmbOfFin rfl j = a :=
    congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨a, has⟩)
  have hk : s.orderEmbOfFin rfl k = b :=
    congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨b, hbs⟩)
  unfold orderedPartitionContribution
  apply Finset.prod_eq_zero hs
  rw [orderedBlockWord_eq_ofFn]
  apply hfree.cumulant_ofFn_eq_zero_of_mixed _ (color ∘ s.orderEmbOfFin rfl)
  · intro i
    exact hmem _
  · exact ⟨j, k, by simpa only [Function.comp_apply, hj, hk] using hneq⟩

end FreeProbability

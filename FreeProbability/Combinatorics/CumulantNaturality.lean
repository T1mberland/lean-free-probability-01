import FreeProbability.Combinatorics.CumulantMultilinear

/-! # Naturality of noncrossing cumulant inversion under letter maps -/

namespace FreeProbability

variable {𝕜 X Y : Type*} [Field 𝕜]

/-- Write the cumulant recursion on a tuple of a prescribed length. -/
noncomputable def cumulantRecursionRhs (M : List X → 𝕜) (n : ℕ) (x : Fin n → X) : 𝕜 :=
  M (List.ofFn x) - ∑ p : ProperNoncrossingPartition n,
    ∏ s ∈ p.val.blocks.attach,
      freeCumulant M (List.ofFn (x ∘ s.val.orderEmbOfFin rfl))

theorem freeCumulant_recursion_tuple (M : List X → 𝕜) {n : ℕ} (x : Fin n → X) (hn : n ≠ 0) :
    freeCumulant M (List.ofFn x) = cumulantRecursionRhs M n x := by
  have hlist (w : List X) (hw : w ≠ []) :
      freeCumulant M w = cumulantRecursionRhs M w.length w.get := by
    rw [freeCumulant_recursion M w hw]
    unfold cumulantRecursionRhs
    simp only [List.ofFn_get]
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    unfold partitionContribution
    apply Finset.prod_congr rfl
    intro s _
    rw [blockWord_eq_ofFn]
  have hx : List.ofFn x ≠ [] := by
    intro he
    have hlen := congrArg List.length he
    simp only [List.length_ofFn, List.length_nil] at hlen
    exact hn hlen
  have h := hlist (List.ofFn x) hx
  rw [apply_ofFn_get (cumulantRecursionRhs M) x] at h
  exact h

/-- Pulling back a moment function along a letter map pulls back its cumulants.
Labels, embeddings, and repeated generators therefore preserve cumulant inversion. -/
theorem freeCumulant_map (M : List Y → 𝕜) (f : X → Y) (w : List X) :
    freeCumulant (M ∘ List.map f) w = freeCumulant M (w.map f) := by
  have htuple : ∀ n (x : Fin n → X),
      freeCumulant (M ∘ List.map f) (List.ofFn x) =
        freeCumulant M (List.ofFn (f ∘ x)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x
      by_cases hn : n = 0
      · subst n
        simp
      rw [freeCumulant_recursion_tuple _ x hn, freeCumulant_recursion_tuple M (f ∘ x) hn]
      unfold cumulantRecursionRhs
      simp only [Function.comp_apply, List.map_ofFn]
      congr 1
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.prod_congr rfl
      intro s _
      exact ih s.val.card (p.val.block_card_lt_of_ne_indiscrete p.property s.property)
        (x ∘ s.val.orderEmbOfFin rfl)
  have h := htuple w.length w.get
  have hmap : List.ofFn (f ∘ w.get) = w.map f := by
    change List.ofFn (fun i => f (w.get i)) = w.map f
    rw [List.ofFn_comp' w.get f, List.ofFn_get]
  rw [hmap] at h
  simpa only [List.ofFn_get] using h

end FreeProbability

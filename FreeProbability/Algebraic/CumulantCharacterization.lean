import FreeProbability.Algebraic.CumulantAdjacentProduct
import FreeProbability.Algebraic.CumulantCenter
import Mathlib.Data.List.ChainOfFn

/-!
# Freeness implies vanishing mixed free cumulants

All-order induction splits into alternating and adjacent-equal-label words.
Centering reduces the alternating case to freeness and singleton blocks. The
adjacent-product identity handles the other case; every proper top-fiber term
has a mixed shorter block. Together with the converse this gives the complete
algebraic characterization, with no extra assumptions on the probability space.
-/

namespace FreeProbability

variable {𝕜 A I : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]

private theorem contribution_zero_of_mixedIH (φ : ProbabilitySpace 𝕜 A)
    (B : I → Subalgebra 𝕜 A) {n : ℕ} (x : Fin n → A) (color : Fin n → I)
    (hmem : ∀ a, x a ∈ B (color a))
    (ih : ∀ m < n, ∀ (y : Fin m → A) (c : Fin m → I),
      (∀ a, y a ∈ B (c a)) → (∃ a b, c a ≠ c b) → cumulant φ (List.ofFn y) = 0)
    (p : NoncrossingPartition n) (hp : p ≠ NoncrossingPartition.indiscrete n)
    (hmix : ¬∀ a b, p.val.r a b → color a = color b) :
    orderedPartitionContribution (cumulant φ) x p = 0 := by
  classical
  obtain ⟨a, ha⟩ := not_forall.mp hmix
  obtain ⟨b, hb⟩ := not_forall.mp ha
  obtain ⟨hab, hcolor⟩ := not_imp.mp hb
  obtain ⟨s, hs, has, hbs⟩ := (p.same_block_iff a b).mpr hab
  have hposa : s.orderEmbOfFin rfl ((s.orderIsoOfFin rfl).symm ⟨a, has⟩) = a :=
    congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨a, has⟩)
  have hposb : s.orderEmbOfFin rfl ((s.orderIsoOfFin rfl).symm ⟨b, hbs⟩) = b :=
    congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨b, hbs⟩)
  unfold orderedPartitionContribution
  apply Finset.prod_eq_zero hs
  rw [orderedBlockWord_eq_ofFn]
  apply ih s.card (p.block_card_lt_of_ne_indiscrete hp hs) (x ∘ s.orderEmbOfFin rfl)
    (color ∘ s.orderEmbOfFin rfl)
  · intro j
    exact hmem _
  · refine ⟨(s.orderIsoOfFin rfl).symm ⟨a, has⟩, (s.orderIsoOfFin rfl).symm ⟨b, hbs⟩, ?_⟩
    simpa only [Function.comp_apply, hposa, hposb] using hcolor

/-- Every mixed cumulant of a freely independent family vanishes, at all orders. -/
theorem FreelyIndependent.cumulant_ofFn_eq_zero_of_mixed {φ : ProbabilitySpace 𝕜 A}
    {B : I → Subalgebra 𝕜 A} (hfree : FreelyIndependent φ B) {n : ℕ}
    (x : Fin n → A) (color : Fin n → I) (hmem : ∀ a, x a ∈ B (color a))
    (hmixed : ∃ a b, color a ≠ color b) : cumulant φ (List.ofFn x) = 0 := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => obtain ⟨a, _, _⟩ := hmixed; exact Fin.elim0 a
    | succ n =>
      by_cases hn : n = 0
      · subst n
        obtain ⟨a, b, hab⟩ := hmixed
        exact False.elim (hab (congrArg color ((Fin.eq_zero a).trans (Fin.eq_zero b).symm)))
      have hn2 : 2 ≤ n + 1 := by omega
      by_cases halt : ∀ i : Fin n, color i.castSucc ≠ color i.succ
      · let y : Fin (n + 1) → A := fun a => φ.center (x a)
        have hymem : ∀ a, y a ∈ B (color a) := fun a => φ.center_mem _ (hmem a)
        have hsep : ∀ a b : Fin (n + 1), a.val + 1 = b.val → color a ≠ color b := by
          intro a b hab
          let j : Fin n := ⟨a.val, by omega⟩
          have ha : j.castSucc = a := Fin.ext rfl
          have hb : j.succ = b := Fin.ext hab
          exact ha ▸ hb ▸ halt j
        let w := List.ofFn (fun a : Fin (n + 1) => (color a, y a))
        have hw : w ≠ [] := by intro he; have hl := congrArg List.length he; simp [w] at hl
        have hchain : w.IsChain (fun a b => a.1 ≠ b.1) := by
          apply List.isChain_ofFn.mpr
          intro k hk
          exact hsep ⟨k, by omega⟩ ⟨k + 1, hk⟩ rfl
        have hmoment : φ.expectation (List.ofFn y).prod = 0 := by
          have hf := hfree w hw hchain
            (by intro a ha; obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha; exact hymem j)
            (by intro a ha; obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha; exact φ.expectation_center _)
          simpa only [w, List.map_ofFn, Function.comp_def] using hf
        have hproper (p : NoncrossingPartition (n + 1)) (hp : p ≠ ⊤) :
            orderedPartitionContribution (cumulant φ) y p = 0 := by
          by_cases hmono : ∀ a b, p.val.r a b → color a = color b
          · obtain ⟨a, ha⟩ := p.exists_singleton_of_alternating_coloring (by omega) color hsep hmono
            have hs := p.singleton_mem_blocks a ha
            unfold orderedPartitionContribution
            apply Finset.prod_eq_zero hs
            simp [orderedBlockWord, cumulant, freeCumulant_singleton, y, φ.expectation_center]
          · apply contribution_zero_of_mixedIH φ B y color hymem ih p
            · simpa only [NoncrossingPartition.top_eq_indiscrete] using hp
            · exact hmono
        have hsum := expectation_eq_sum_orderedCumulants φ y
        rw [Fintype.sum_eq_single (⊤ : NoncrossingPartition (n + 1))] at hsum
        · rw [NoncrossingPartition.top_eq_indiscrete,
            orderedPartitionContribution_indiscrete φ y (by omega), hmoment] at hsum
          rw [← cumulant_ofFn_center φ hn2 x]
          exact hsum.symm
        · intro p hp
          exact hproper p hp
      · obtain ⟨i, hi⟩ := not_forall.mp halt
        have hcolor : color i.castSucc = color i.succ := not_not.mp hi
        let c : Fin n → I := color ∘ i.castSucc.succAbove
        have hcmem : ∀ a, fuseAdjacent x i a ∈ B (c a) := by
          intro a
          by_cases hai : a = i
          · subst a
            have hl : x i.castSucc ∈ B (color i.succ) := hcolor ▸ hmem i.castSucc
            simpa only [fuseAdjacent_at, c, Function.comp_apply, Fin.succAbove_castSucc_self]
              using (B (color i.succ)).mul_mem hl (hmem i.succ)
          · simpa [fuseAdjacent, hai, c] using hmem (i.castSucc.succAbove a)
        have hcolors (a : Fin (n + 1)) : color a = c (i.predAbove a) := by
          by_cases ha : a = i.castSucc
          · subst a
            simpa only [c, Function.comp_apply, Fin.predAbove_castSucc_self,
              Fin.succAbove_castSucc_self] using hcolor
          · simp only [c, Function.comp_apply, Fin.succAbove_predAbove ha]
        have hcmixed : ∃ a b, c a ≠ c b := by
          obtain ⟨a, b, hab⟩ := hmixed
          refine ⟨i.predAbove a, i.predAbove b, ?_⟩
          intro he
          exact hab ((hcolors a).trans (he.trans (hcolors b).symm))
        have hzero := ih n (by omega) (fuseAdjacent x i) c hcmem hcmixed
        have hf := cumulant_fuseAdjacent φ x i
        rw [Fintype.sum_eq_single
          (⟨⊤, top_sup_eq _⟩ : AdjacentPartitionFiber (⊤ : NoncrossingPartition (n + 1)) i)] at hf
        · change cumulant φ (List.ofFn (fuseAdjacent x i)) =
            orderedPartitionContribution (cumulant φ) x (⊤ : NoncrossingPartition (n + 1)) at hf
          rw [NoncrossingPartition.top_eq_indiscrete,
            orderedPartitionContribution_indiscrete φ x (by omega), hzero] at hf
          exact hf.symm
        · intro p hp
          apply contribution_zero_of_mixedIH φ B x color hmem ih p.val
          · intro he
            apply hp
            exact Subtype.ext (by simpa only [NoncrossingPartition.top_eq_indiscrete] using he)
          · intro hmono
            have hall := p.val.monochromatic_of_sup_adjacentPair_eq_top i color p.property hcolor hmono
            obtain ⟨a, b, hab⟩ := hmixed
            exact hab ((hall a).trans (hall b).symm)

/-- Freeness implies the original labeled all-order mixed-cumulant vanishing condition. -/
theorem FreelyIndependent.mixedCumulantsVanish {φ : ProbabilitySpace 𝕜 A}
    {B : I → Subalgebra 𝕜 A} (hfree : FreelyIndependent φ B) : MixedCumulantsVanish φ B := by
  intro w hmem hmixed
  rw [labeledCumulant_eq]
  have h := hfree.cumulant_ofFn_eq_zero_of_mixed (fun i => (w.get i).2) (fun i => (w.get i).1)
    (fun i => hmem _ (List.get_mem _ _))
  have hm : ∃ i j : Fin w.length, (w.get i).1 ≠ (w.get j).1 := by
    obtain ⟨a, ha, b, hb, hab⟩ := hmixed
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ha
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hb
    exact ⟨i, j, hab⟩
  have hfinal := h hm
  rw [List.ofFn_comp' w.get Prod.snd, List.ofFn_get] at hfinal
  exact hfinal

/-- The complete freeness–mixed-cumulant characterization. -/
theorem freelyIndependent_iff_mixedCumulantsVanish (φ : ProbabilitySpace 𝕜 A)
    (B : I → Subalgebra 𝕜 A) : FreelyIndependent φ B ↔ MixedCumulantsVanish φ B :=
  ⟨FreelyIndependent.mixedCumulantsVanish, MixedCumulantsVanish.freelyIndependent⟩

end FreeProbability

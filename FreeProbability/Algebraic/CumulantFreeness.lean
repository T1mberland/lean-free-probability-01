import FreeProbability.Combinatorics.NoncrossingSingleton
import FreeProbability.Combinatorics.CumulantMultilinear
import FreeProbability.Combinatorics.CumulantNaturality

/-!
# Mixed-cumulant vanishing implies freeness

Cumulants of labeled words use the moment function that forgets labels and
multiplies algebra entries. Every partition term of a centered alternating word
vanishes: a mixed block has zero cumulant, and an entirely monochromatic
partition has a centered singleton block.

The reverse implication is a separate remaining theorem.
-/

namespace FreeProbability

variable {𝕜 A I : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]

instance : IsEmpty (ProperNoncrossingPartition 1) :=
  ⟨fun p => p.property (Subsingleton.elim _ _)⟩

@[simp] theorem freeCumulant_singleton {X : Type*} (moment : List X → 𝕜) (x : X) :
    freeCumulant moment [x] = moment [x] := by
  rw [freeCumulant_recursion moment [x] (by simp)]
  simp

/-- Cumulants of a word with subalgebra labels, obtained by inverting its actual moments. -/
noncomputable def labeledCumulant (φ : ProbabilitySpace 𝕜 A) (w : List (I × A)) : 𝕜 :=
  freeCumulant (fun w => φ.expectation (wordProduct w)) w

/-- Labels do not change the underlying algebra-valued cumulant. -/
theorem labeledCumulant_eq (φ : ProbabilitySpace 𝕜 A) (w : List (I × A)) :
    labeledCumulant φ w = cumulant φ (w.map Prod.snd) :=
  freeCumulant_map (fun w => φ.expectation w.prod) Prod.snd w

/-- Vanishing of every cumulant involving letters from more than one subalgebra. -/
def MixedCumulantsVanish (φ : ProbabilitySpace 𝕜 A) (B : I → Subalgebra 𝕜 A) : Prop :=
  ∀ w : List (I × A), (∀ x ∈ w, x.2 ∈ B x.1) →
    (∃ x ∈ w, ∃ y ∈ w, x.1 ≠ y.1) → labeledCumulant φ w = 0

theorem MixedCumulantsVanish.freelyIndependent {φ : ProbabilitySpace 𝕜 A}
    {B : I → Subalgebra 𝕜 A} (h : MixedCumulantsVanish φ B) : FreelyIndependent φ B := by
  classical
  intro w hne halt hmem hcenter
  let M : List (I × A) → 𝕜 := fun v => φ.expectation (wordProduct v)
  have hM := moment_cumulant_formula M w hne
  change M w = 0
  rw [hM]
  apply Finset.sum_eq_zero
  intro p _
  have hmblock (s : Finset (Fin w.length)) :
      ∀ x ∈ blockWord w s, x.2 ∈ B x.1 := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact hmem (w.get i) (List.get_mem _ _)
  by_cases hmixed : ∃ s ∈ p.blocks,
      ∃ x ∈ blockWord w s, ∃ y ∈ blockWord w s, x.1 ≠ y.1
  · obtain ⟨s, hs, hmix⟩ := hmixed
    unfold partitionContribution
    apply Finset.prod_eq_zero (i := ⟨s, hs⟩) (Finset.mem_attach _ _)
    exact h (blockWord w s) (hmblock s) hmix
  · have hmono : ∀ i j, p.val.r i j → (w.get i).1 = (w.get j).1 := by
      intro i j hij
      obtain ⟨s, hs, his, hjs⟩ := (p.same_block_iff i j).mpr hij
      have hiw : w.get i ∈ blockWord w s :=
        List.mem_map.mpr ⟨i, by simpa using his, rfl⟩
      have hjw : w.get j ∈ blockWord w s :=
        List.mem_map.mpr ⟨j, by simpa using hjs, rfl⟩
      by_contra hneq
      exact hmixed ⟨s, hs, w.get i, hiw, w.get j, hjw, hneq⟩
    have ha : ∀ i j : Fin w.length, i.val + 1 = j.val → (w.get i).1 ≠ (w.get j).1 := by
      intro i j hij
      have hj : i.val + 1 < w.length := hij ▸ j.isLt
      have hpair := halt.getElem i.val hj
      simpa only [List.get_eq_getElem, hij] using hpair
    obtain ⟨i, hi⟩ := p.exists_singleton_of_alternating_coloring
      (List.length_pos_iff.mpr hne) (fun i => (w.get i).1) ha hmono
    have hs := p.singleton_mem_blocks i hi
    unfold partitionContribution
    apply Finset.prod_eq_zero (i := ⟨{i}, hs⟩) (Finset.mem_attach _ _)
    simp only [blockWord, Finset.sort_singleton, List.map_singleton, freeCumulant_singleton]
    simpa [M, wordProduct] using hcenter (w.get i) (List.get_mem _ _)

end FreeProbability

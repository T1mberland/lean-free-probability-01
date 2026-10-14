import FreeProbability.Algebraic.FreenessGroupingInterval
import Mathlib.Data.List.Pairwise

/-! # Ordered packing of arbitrary finite tuples of words -/

noncomputable section
open scoped Classical
namespace FreeProbability

/-- Ordered block extraction from a list is exactly filtering its positions. -/
theorem orderedBlockWord_get_filter {X : Type*} (l : List X) (P : X → Bool) :
    orderedBlockWord l.get (Finset.univ.filter (fun i => P (l.get i))) = l.filter P := by
  have hsort : (Finset.univ.filter (fun i : Fin l.length => P (l.get i))).sort =
      (List.finRange l.length).filter (fun i => P (l.get i)) := by
    apply Finset.sortedLT_sort _ |>.eq_of_mem_iff
      (List.sortedLT_iff_pairwise.mpr
        (List.Pairwise.filter _ (List.sortedLT_finRange _).pairwise))
    intro i
    simp
  rw [orderedBlockWord, hsort]
  have hmap := List.filter_map (f := l.get) (p := P) (l := List.finRange l.length)
  simp only [Function.comp_def] at hmap
  rw [← hmap, ← List.ofFn_eq_map, List.ofFn_get]

/-- Packing retains every original word's macro position as an explicit tag. -/
def groupedTaggedWord {X : Type*} {m : ℕ} (w : Fin m → List X) : List (Fin m × X) :=
  (List.ofFn (fun i => (w i).map (fun x => (i, x)))).flatten

private theorem flatten_ofFn_single {X : Type*} {m : ℕ} (i : Fin m) (l : List X) :
    (List.ofFn (fun j => if j = i then l else [])).flatten = l := by
  induction m with
  | zero => exact i.elim0
  | succ m ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [List.ofFn_succ]
      simp
    · rw [List.ofFn_succ]
      simpa [Ne.symm (Fin.succ_ne_zero j)] using ih j

/-- The packed tag sequence is ordered, regardless of word lengths. -/
theorem groupedTaggedWord_pairwise {X : Type*} {m : ℕ} (w : Fin m → List X) :
    (groupedTaggedWord w).Pairwise (fun a b => a.1 ≤ b.1) := by
  rw [groupedTaggedWord, List.pairwise_flatten]
  constructor
  · intro l hl
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
    rw [List.pairwise_map]
    exact List.pairwise_of_forall (fun _ _ => le_rfl)
  · apply List.pairwise_ofFn.mpr
    intro i j hij a ha b hb
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hb
    exact hij.le

/-- Filtering by a macro position recovers its original word in exact order. -/
theorem groupedTaggedWord_filter {X : Type*} {m : ℕ} (w : Fin m → List X) (i : Fin m) :
    (groupedTaggedWord w).filter (fun a => decide (a.1 = i)) = (w i).map (fun x => (i, x)) := by
  rw [groupedTaggedWord, List.filter_flatten, List.map_ofFn]
  have h (j : Fin m) : ((w j).map (fun x => (j, x))).filter (fun a => decide (a.1 = i)) =
      if j = i then (w i).map (fun x => (i, x)) else [] := by
    by_cases hj : j = i
    · subst j
      simp
    · simp only [hj, ite_false]
      apply List.filter_eq_nil_iff.mpr
      intro a ha
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
      simp [hj]
  simp only [Function.comp_def]
  simp_rw [h]
  exact flatten_ofFn_single i _

/-- The literal macro-position map of the ordered packed word. -/
def groupedWordQuotient {X : Type*} {m : ℕ} (w : Fin m → List X) :
    Fin (groupedTaggedWord w).length → Fin m := fun k => ((groupedTaggedWord w).get k).1

/-- Packed macro positions form a monotone quotient. -/
theorem groupedWordQuotient_monotone {X : Type*} {m : ℕ} (w : Fin m → List X) :
    Monotone (groupedWordQuotient w) := by
  intro a b hab
  rcases hab.eq_or_lt with h | h
  · subst b
    exact le_rfl
  · have hp := groupedTaggedWord_pairwise w
    rw [List.pairwise_iff_get] at hp
    exact hp a b h

/-- Nonempty macro words make the actual quotient surjective. -/
theorem groupedWordQuotient_surjective {X : Type*} {m : ℕ} (w : Fin m → List X)
    (hw : ∀ i, w i ≠ []) : Function.Surjective (groupedWordQuotient w) := by
  intro i
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil (w i) (hw i)
  have hm : (i, x) ∈ groupedTaggedWord w := by
    apply List.mem_flatten.mpr
    refine ⟨(w i).map (fun x => (i, x)), List.mem_ofFn.mpr ⟨i, rfl⟩, ?_⟩
    exact List.mem_map.mpr ⟨x, hx, rfl⟩
  obtain ⟨k, hk⟩ := List.get_of_mem hm
  exact ⟨k, congrArg Prod.fst hk⟩
/-- Packed membership remembers exactly which original word contains a letter. -/
theorem mem_groupedTaggedWord_iff {X : Type*} {m : ℕ} (w : Fin m → List X)
    (a : Fin m × X) : a ∈ groupedTaggedWord w ↔ a.2 ∈ w a.1 := by
  constructor
  · intro ha
    obtain ⟨l, hl, hal⟩ := List.mem_flatten.mp ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hal
    exact hx
  · intro ha
    apply List.mem_flatten.mpr
    refine ⟨(w a.1).map (fun x => (a.1, x)), List.mem_ofFn.mpr ⟨a.1, rfl⟩, ?_⟩
    exact List.mem_map.mpr ⟨a.2, ha, by cases a; rfl⟩

/-- The actual ordered quotient fiber is the original macro word, exactly. -/
theorem orderedBlockWord_groupedWord_fiber {X : Type*} {m : ℕ}
    (w : Fin m → List X) (i : Fin m) :
    orderedBlockWord (fun k => ((groupedTaggedWord w).get k).2)
      (Finset.univ.filter (fun k => groupedWordQuotient w k = i)) = w i := by
  have hmap : ∀ s, orderedBlockWord (fun k => ((groupedTaggedWord w).get k).2) s =
      (orderedBlockWord (groupedTaggedWord w).get s).map Prod.snd := by
    intro s
    simp only [orderedBlockWord, List.map_map, Function.comp_def]
  rw [hmap]
  have hword := orderedBlockWord_get_filter (groupedTaggedWord w)
    (fun a => decide (a.1 = i))
  simp only [decide_eq_true_eq] at hword
  change orderedBlockWord (groupedTaggedWord w).get
    (Finset.univ.filter (fun k => groupedWordQuotient w k = i)) = _ at hword
  rw [hword, groupedTaggedWord_filter]
  simp [List.map_map]

/-- Literal interval products of the packing are exactly the original products. -/
theorem intervalProducts_groupedWord {A : Type*} [Monoid A] {m : ℕ}
    (w : Fin m → List A) :
    intervalProducts (groupedWordQuotient w) (fun k => ((groupedTaggedWord w).get k).2) =
      fun i => (w i).prod := by
  funext i
  exact congrArg List.prod (orderedBlockWord_groupedWord_fiber w i)

variable {𝕜 A I J : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]

/-- Arbitrary word products from each grouped family have vanishing mixed
cumulant, including words of length zero. This is the generator-product step
for grouping the entire generated algebras. -/
theorem FreelyIndependent.cumulant_wordProducts_eq_zero_of_grouped_mixed
    {φ : ProbabilitySpace 𝕜 A} {B : I → Subalgebra 𝕜 A} (hf : FreelyIndependent φ B)
    (g : I → J) {m : ℕ} (label : Fin m → J) (w : Fin m → List A)
    (hletters : ∀ k a, a ∈ w k → ∃ i, g i = label k ∧ a ∈ B i)
    (hmixed : ∃ a b, label a ≠ label b) :
    cumulant φ (List.ofFn (fun k => (w k).prod)) = 0 := by
  by_cases hne : ∀ k, w k ≠ []
  · let f := groupedWordQuotient w
    let x := fun k => ((groupedTaggedWord w).get k).2
    have hgen (k : Fin (groupedTaggedWord w).length) :
        ∃ i, g i = label (f k) ∧ x k ∈ B i :=
      hletters (f k) (x k)
        ((mem_groupedTaggedWord_iff w _).mp (List.get_mem _ _))
    let color := fun k => Classical.choose (hgen k)
    have h := hf.cumulant_intervalProducts_eq_zero_of_grouped_mixed g f
      (groupedWordQuotient_monotone w) (groupedWordQuotient_surjective w hne) x color label
      (fun k => (Classical.choose_spec (hgen k)).2)
      (fun k => (Classical.choose_spec (hgen k)).1) hmixed
    simpa only [f, x, intervalProducts_groupedWord] using h
  · obtain ⟨k, hk⟩ := not_forall.mp hne
    have he : w k = [] := Classical.not_not.mp hk
    obtain ⟨a, b, hab⟩ := hmixed
    have hm : 2 ≤ m := by
      have ha := a.isLt
      have hb := b.isLt
      by_contra h
      have heq : a = b := Fin.ext (by omega)
      exact hab (congrArg label heq)
    apply cumulant_ofFn_eq_zero_of_unit φ hm _ k
    simp only [he, List.prod_nil]
end FreeProbability

import FreeProbability.RandomMatrix.OrthogonalColoredTraceIndependence
import Mathlib.Data.List.SplitBy

/-! # Actual selected-color segmentation of ordered words -/

noncomputable section
open scoped Classical
namespace FreeProbability.Orthogonal
variable {α I : Type*}

/-- Split an actual ordered word just before each occurrence of the selected
color. No occurrence enumeration or supplied factorization is assumed. -/
def selectedColorSegments (color : α → I) (c : I) (word : List α) : List (List α) :=
  word.splitBy (fun _ b => decide (color b ≠ c))

/-- The ACTUAL segments flatten back to the original ordered word. -/
theorem selectedColorSegments_flatten (color : α → I) (c : I) (word : List α) :
    (selectedColorSegments color c word).flatten = word := List.flatten_splitBy _ _

/-- Every actual segment is nonempty. -/
theorem selectedColorSegments_ne_nil (color : α → I) (c : I) (word : List α)
    (s : List α) (hs : s ∈ selectedColorSegments color c word) : s ≠ [] :=
  List.ne_nil_of_mem_splitBy hs

private theorem all_of_chain_targets {β : Type*} (P : β → Prop) (l : List β)
    (hc : l.IsChain (fun _ b => P b)) (hh : ∀ a ∈ l.head?, P a) : ∀ a ∈ l, P a := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.isChain_cons] at hc
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hh b (by simp)
    · exact ih hc.2 hc.1 b hb

/-- If the original word starts with the selected color, EVERY actual
segment starts with that color, not just the first one. -/
theorem selectedColorSegments_heads (color : α → I) (c : I) (word : List α)
    (hw : word ≠ []) (hfirst : color (word.head hw) = c)
    (s : List α) (hs : s ∈ selectedColorSegments color c word) :
    color (s.head (selectedColorSegments_ne_nil color c word s hs)) = c := by
  let P : List α → Prop := fun s => ∀ h : s ≠ [], color (s.head h) = c
  have hc : (selectedColorSegments color c word).IsChain (fun _ b => P b) := by
    apply (List.isChain_getLast_head_splitBy (fun _ b => decide (color b ≠ c)) word).imp
    intro a b hab
    obtain ⟨ha, hb, hrel⟩ := hab
    intro _
    simpa using hrel
  have hsn : selectedColorSegments color c word ≠ [] := List.splitBy_ne_nil.mpr hw
  have hh : ∀ s ∈ (selectedColorSegments color c word).head?, P s := by
    intro s hs hn
    rw [List.head?_eq_some_head hsn] at hs
    simp only [Option.mem_some_iff] at hs
    subst s
    have he := List.head_head_splitBy (fun _ b => decide (color b ≠ c)) hw
    exact (congrArg color he).trans hfirst
  exact all_of_chain_targets P _ hc hh s hs _

/-- All actual letters after a segment's selected head have OTHER colors. -/
theorem selectedColorSegments_tail_colors (color : α → I) (c : I) (word : List α)
    (s : List α) (hs : s ∈ selectedColorSegments color c word) :
    ∀ a ∈ s.tail, color a ≠ c := by
  have hc : s.IsChain (fun _ b => color b ≠ c) := by
    apply (List.isChain_of_mem_splitBy hs).imp
    intro a b h
    simpa using h
  cases s with
  | nil => simp
  | cons a l =>
    rw [List.isChain_cons] at hc
    exact all_of_chain_targets (fun b => color b ≠ c) l hc.2 hc.1

/-- Segmentation preserves the original noncommutative ordered product. -/
theorem selectedColorSegments_orderedProduct {R : Type*} [Monoid R]
    (color : α → I) (c : I) (word : List α) (f : α → R) :
    (word.map f).prod = ((selectedColorSegments color c word).map (fun s => (s.map f).prod)).prod := by
  conv_lhs => rw [← selectedColorSegments_flatten color c word]
  rw [List.map_flatten, List.prod_flatten]
  simp only [List.map_map, Function.comp_def]

/-- A run tail inherits actual adjacent color alternation from the original word. -/
theorem selectedColorSegments_tail_alternating (color : α → I) (c : I) (word : List α)
    (hword : word.IsChain (fun a b => color a ≠ color b))
    (s : List α) (hs : s ∈ selectedColorSegments color c word) :
    s.tail.IsChain (fun a b => color a ≠ color b) := by
  have he : (selectedColorSegments color c word).flatten.IsChain (fun a b => color a ≠ color b) := by
    simpa only [selectedColorSegments_flatten] using hword
  have hn : [] ∉ selectedColorSegments color c word := List.nil_notMem_splitBy _ _
  exact ((List.isChain_flatten hn).mp he).1 s hs |>.tail

/-- Every actual run tail is STRICTLY shorter than the original word. -/
theorem selectedColorSegments_tail_length_lt (color : α → I) (c : I) (word : List α)
    (s : List α) (hs : s ∈ selectedColorSegments color c word) : s.tail.length < word.length := by
  have hn := selectedColorSegments_ne_nil color c word s hs
  have hl := (List.sublist_flatten_of_mem hs).length_le
  rw [selectedColorSegments_flatten] at hl
  cases s with
  | nil => exact False.elim (hn rfl)
  | cons a l => simp only [List.tail_cons, List.length_cons] at hl ⊢; omega

/-- For an actual cyclically alternating word beginning in the selected color,
every other-color run is nonempty. No run nonemptiness premise is supplied. -/
theorem selectedColorSegments_tail_ne_nil (color : α → I) (c : I) (word : List α)
    (hw : word ≠ []) (hfirst : color (word.head hw) = c)
    (hlast : color (word.getLast hw) ≠ c) (hword : word.IsChain (fun a b => color a ≠ color b))
    (s : List α) (hs : s ∈ selectedColorSegments color c word) : s.tail ≠ [] := by
  let L := selectedColorSegments color c word
  let P : List α → Prop := fun a => ∀ h : a ≠ [], color (a.getLast h) ≠ c
  have hLn : L ≠ [] := List.splitBy_ne_nil.mpr hw
  have hnil : [] ∉ L := List.nil_notMem_splitBy _ _
  have hflat : L.flatten.IsChain (fun a b => color a ≠ color b) := by
    simpa only [L, selectedColorSegments_flatten] using hword
  have hboundary := ((List.isChain_flatten hnil).mp hflat).2
  have hc : L.IsChain (fun a _ => P a) := by
    apply hboundary.imp_of_mem_imp
    intro a b ha hb hab hane
    have hbne := selectedColorSegments_ne_nil color c word b hb
    have hheadb := selectedColorSegments_heads color c word hw hfirst b hb
    have hrel := hab (a.getLast hane) (by simp [List.getLast?_eq_some_getLast hane])
      (b.head hbne) (by simp [List.head?_eq_some_head hbne])
    rw [hheadb] at hrel
    exact hrel
  have hh : ∀ a ∈ L.getLast?, P a := by
    intro a ha hane
    rw [List.getLast?_eq_some_getLast hLn] at ha
    simp only [Option.mem_some_iff] at ha
    subst a
    have he := List.getLast_getLast_splitBy (fun _ b => decide (color b ≠ c)) hw
    intro hEq
    exact hlast ((congrArg color he).symm.trans hEq)
  have hr : L.reverse.IsChain (fun _ b => P b) := List.isChain_reverse.mpr hc
  have hhr : ∀ a ∈ L.reverse.head?, P a := by simpa only [List.head?_reverse] using hh
  have hall := all_of_chain_targets P L.reverse hr hhr
  have hne := selectedColorSegments_ne_nil color c word s hs
  have hhead := selectedColorSegments_heads color c word hw hfirst s hs
  have hlasts := hall s (List.mem_reverse.mpr hs) hne
  cases s with
  | nil => exact False.elim (hne rfl)
  | cons a l =>
    change l ≠ []
    intro hl
    subst l
    simp only [List.head_cons, List.getLast_singleton] at hhead hlasts
    exact hlasts hhead

end FreeProbability.Orthogonal

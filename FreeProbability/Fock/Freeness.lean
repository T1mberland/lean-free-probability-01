import FreeProbability.Fock.OneColorWick
import FreeProbability.Algebraic.Freeness

/-! # Direct freeness of the concrete semicircular polynomial algebras -/

noncomputable section
open scoped Classical InnerProductSpace

namespace FreeProbability.Fock

variable {I : Type*}

/-- The algebraic subspace of finite word amplitudes starting in a fixed color. -/
def colorSector (i : I) : Submodule ℂ (WordSpace I) :=
  Submodule.span ℂ (Set.range (fun w => word (i :: w)))

/-- Every vector in a nonempty color sector is orthogonal to the vacuum. -/
theorem inner_vacuum_eq_zero_of_mem_colorSector (i : I) {f : WordSpace I}
    (hf : f ∈ colorSector i) : inner ℂ (vacuum : WordSpace I) f = 0 := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨w, rfl⟩ := hf
    simp only [vacuum, inner_word]
    simp
  | zero => simp
  | add f g hf hg ihf ihg => simp [inner_add_right, ihf, ihg]
  | smul c f hf ihf => simp [inner_smul_right, ihf]

/-- A centered one-color polynomial prefixes a nonempty color block to a foreign word. -/
theorem positive_apply_word_mem_colorSector (i : I)
    {T : WordSpace I →L[ℂ] WordSpace I} (hT : T ∈ positiveOneColorSpan i)
    (w : List I) (hw : ∀ j v, w = j :: v → i ≠ j) : T (word w) ∈ colorSector i := by
  induction hT using Submodule.span_induction with
  | mem T hT =>
    obtain ⟨n, rfl⟩ := hT
    rw [oneColorWick_word i (n + 1) w hw, List.replicate_succ, List.cons_append]
    exact Submodule.subset_span ⟨List.replicate n i ++ w, rfl⟩
  | zero => simp
  | add T U hT hU ihT ihU => simpa using (colorSector i).add_mem ihT ihU
  | smul c T hT ihT => simpa using (colorSector i).smul_mem c ihT

/-- A centered polynomial of a different color carries an entire foreign sector into its own. -/
theorem positive_apply_colorSector (i j : I) (hij : i ≠ j)
    {T : WordSpace I →L[ℂ] WordSpace I} (hT : T ∈ positiveOneColorSpan i)
    {f : WordSpace I} (hf : f ∈ colorSector j) : T f ∈ colorSector i := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨w, rfl⟩ := hf
    apply positive_apply_word_mem_colorSector i hT (j :: w)
    intro k v hk
    cases hk
    exact hij
  | zero => simp
  | add f g hf hg ihf ihg => simpa [map_add] using (colorSector i).add_mem ihf ihg
  | smul c f hf ihf => simpa [map_smul] using (colorSector i).smul_mem c ihf

/-- Alternating products of arbitrary positive-degree Wick expansions lie in the first sector. -/
theorem alternating_positive_product_mem_colorSector
    (a : I × (WordSpace I →L[ℂ] WordSpace I))
    (w : List (I × (WordSpace I →L[ℂ] WordSpace I)))
    (halt : (a :: w).IsChain (fun x y => x.1 ≠ y.1))
    (hmem : ∀ x ∈ a :: w, x.2 ∈ positiveOneColorSpan x.1) :
    ((a :: w).map Prod.snd).prod (vacuum : WordSpace I) ∈ colorSector a.1 := by
  induction w generalizing a with
  | nil =>
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    exact positive_apply_word_mem_colorSector a.1 (hmem a (by simp)) [] (by simp)
  | cons b w ih =>
    have hchain := List.isChain_cons_cons.mp halt
    have hf := ih b hchain.2 (fun x hx => hmem x (by simp [hx]))
    simp only [List.map_cons, List.prod_cons, mul_apply_eq_comp]
    exact positive_apply_colorSector a.1 b.1 hchain.1 (hmem a (by simp)) hf

/-- The concrete one-generator polynomial algebras are freely independent.
This quantifies over all centered polynomials of arbitrary degree and all finite alternating words. -/
theorem freelyIndependent_semicircular_polynomial (I : Type*) :
    FreelyIndependent (vacuumState I).toProbabilitySpace
      (fun i => Algebra.adjoin ℂ ({semicircular i} : Set (WordSpace I →L[ℂ] WordSpace I))) := by
  intro w hw halt hmem hzero
  cases w with
  | nil => exact (hw rfl).elim
  | cons a w =>
    apply inner_vacuum_eq_zero_of_mem_colorSector a.1
    apply alternating_positive_product_mem_colorSector a w halt
    intro x hx
    exact centered_mem_positiveOneColorSpan x.1 (hmem x hx) (hzero x hx)

end FreeProbability.Fock

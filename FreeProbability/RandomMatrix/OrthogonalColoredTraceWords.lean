import FreeProbability.RandomMatrix.OrthogonalColoredTraceSegments

/-! # Actual colored conjugation words and selected-color matrix runs -/

noncomputable section
open scoped Classical Topology
namespace FreeProbability.Orthogonal
open Matrix
variable {α I n : Type*} [Fintype n] [DecidableEq n]

/-- An actual colored orthogonal conjugation factor. -/
def coloredConjugateBlock (color : α → I) (A : α → Matrix n n ℂ) (U : I → Group n) (a : α) :
    Matrix n n ℂ := complexMatrix (U (color a)) * A a * (complexMatrix (U (color a))).transpose

/-- The actual normalized trace of the entire ordered colored word. -/
def coloredTraceWord (color : α → I) (word : List α) (A : α → Matrix n n ℂ) (U : I → Group n) : ℂ :=
  normalizedTrace (word.map (coloredConjugateBlock color A U)).prod

/-- The actual selected-color occurrence starting each actual segment. -/
def selectedColorHead (color : α → I) (c : I) (word : List α)
    (k : Fin (selectedColorSegments color c word).length) : α :=
  ((selectedColorSegments color c word).get k).head
    (selectedColorSegments_ne_nil color c word _ (List.get_mem _ k))

/-- The actual other-color run after that occurrence. -/
def selectedColorRun (color : α → I) (c : I) (word : List α)
    (k : Fin (selectedColorSegments color c word).length) : List α :=
  ((selectedColorSegments color c word).get k).tail

/-- The actual ordered product over the other-color run. -/
def selectedColorRunMatrix (color : α → I) (c : I) (word : List α)
    (A : α → Matrix n n ℂ) (U : I → Group n)
    (k : Fin (selectedColorSegments color c word).length) : Matrix n n ℂ :=
  ((selectedColorRun color c word k).map (coloredConjugateBlock color A U)).prod

/-- The actual word is exactly a single selected-color conjugation word with
the actual other-color run products, in the original order. -/
theorem coloredTraceWord_eq_selected (color : α → I) (c : I) (word : List α)
    (hw : word ≠ []) (hfirst : color (word.head hw) = c)
    (A : α → Matrix n n ℂ) (U : I → Group n) :
    coloredTraceWord color word A U = traceWord (fun k => A (selectedColorHead color c word k))
      (selectedColorRunMatrix color c word A U) (U c) := by
  have hseg (k : Fin (selectedColorSegments color c word).length) :
      (((selectedColorSegments color c word).get k).map (coloredConjugateBlock color A U)).prod =
      complexMatrix (U c) * A (selectedColorHead color c word k) * (complexMatrix (U c)).transpose *
        selectedColorRunMatrix color c word A U k := by
    let s := (selectedColorSegments color c word).get k
    have hs : s ∈ selectedColorSegments color c word := List.get_mem _ k
    have hn := selectedColorSegments_ne_nil color c word s hs
    have hh := selectedColorSegments_heads color c word hw hfirst s hs
    have he : s = s.head hn :: s.tail := (List.cons_head_tail hn).symm
    change (s.map (coloredConjugateBlock color A U)).prod = _
    conv_lhs => rw [he, List.map_cons, List.prod_cons]
    change coloredConjugateBlock color A U (s.head hn) *
      (s.tail.map (coloredConjugateBlock color A U)).prod = _
    unfold coloredConjugateBlock
    rw [hh]
    rfl
  unfold coloredTraceWord traceWord
  rw [selectedColorSegments_orderedProduct color c word]
  have he := congrArg (fun L => (L.map (fun s => (s.map (coloredConjugateBlock color A U)).prod)).prod)
    (List.ofFn_get (selectedColorSegments color c word)).symm
  rw [he, List.map_ofFn]
  exact congrArg normalizedTrace (congrArg (fun f => (List.ofFn f).prod) (funext hseg))

/-- Actual colored conjugation preserves the literal Euclidean operator norm. -/
theorem coloredConjugateBlock_opNorm (color : α → I) (A : α → Matrix n n ℂ) (U : I → Group n) (a : α) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (coloredConjugateBlock color A U a)‖ =
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A a)‖ := by
  open scoped Matrix.Norms.L2Operator in
    have hu := complexMatrix_mem_unitary (U (color a))
    have ht := Matrix.transpose_mem_unitaryGroup_iff.mpr hu
    have he : ‖coloredConjugateBlock color A U a‖ = ‖A a‖ := by
      unfold coloredConjugateBlock
      rw [CStarRing.norm_mul_mem_unitary _ ht, CStarRing.norm_mem_unitary_mul _ hu]
    simpa only [Matrix.cstar_norm_def] using he

/-- Every actual finite colored matrix word has the genuine uniform operator
product bound; the empty word and dimension zero are included. -/
theorem coloredWordProduct_opNorm_le (color : α → I) (word : List α)
    (A : α → Matrix n n ℂ) (U : I → Group n) (K : ℝ) (hK : 0 ≤ K)
    (hA : ∀ a ∈ word, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A a)‖ ≤ K) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (word.map (coloredConjugateBlock color A U)).prod‖ ≤ K ^ word.length := by
  have hb := orderedProduct_Euclidean_opNorm_le K hK
    (fun k : Fin word.length => coloredConjugateBlock color A U (word.get k)) (fun k => by
      rw [coloredConjugateBlock_opNorm]
      exact hA _ (List.get_mem word k))
  have he : (List.ofFn (fun k : Fin word.length => coloredConjugateBlock color A U (word.get k))) =
      word.map (coloredConjugateBlock color A U) := by
    change List.ofFn (coloredConjugateBlock color A U ∘ word.get) = _
    rw [← List.map_ofFn, List.ofFn_get]
  rwa [he] at hb

/-- The actual normalized colored trace inherits the genuine uniform bound. -/
theorem coloredTraceWord_norm_le (color : α → I) (word : List α)
    (A : α → Matrix n n ℂ) (U : I → Group n) (K : ℝ) (hK : 0 ≤ K)
    (hA : ∀ a ∈ word, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A a)‖ ≤ K) :
    ‖coloredTraceWord color word A U‖ ≤ K ^ word.length :=
  (normalizedTrace_norm_le_Euclidean_opNorm _).trans (coloredWordProduct_opNorm_le color word A U K hK hA)

end FreeProbability.Orthogonal

import FreeProbability.RandomMatrix.OrthogonalColoredTraceVariableData

/-! # Actual measurable selected-color run data -/

noncomputable section
open scoped Classical
namespace FreeProbability.Orthogonal
open Matrix MeasureTheory
variable {α I n Θ : Type*} [Fintype n] [DecidableEq n]

/-- For data construction only, fill the missing selected-color coordinate
by the genuine group identity. All run letters have other colors. -/
def exceptHaarColor (c d : I) (z : ExceptHaarData Θ I n c) : Group n :=
  if h : d = c then 1 else exceptHaarMatrix c d h z

/-- The filled coordinate map is genuinely measurable. -/
theorem measurable_exceptHaarColor [MeasurableSpace Θ] (c d : I) :
    Measurable (exceptHaarColor (Θ := Θ) (n := n) c d) := by
  by_cases h : d = c
  · have he : exceptHaarColor (Θ := Θ) (n := n) c d = fun _ => 1 := by
      funext z
      simp [exceptHaarColor, h]
    rw [he]
    exact measurable_const
  · have he : exceptHaarColor (Θ := Θ) (n := n) c d = exceptHaarMatrix c d h := by
      funext z
      simp [exceptHaarColor, h]
    rw [he]
    exact measurable_exceptHaarMatrix c d h

/-- Every nonselected coordinate is exactly the actual matrix in a realization. -/
theorem exceptHaarColor_apply {Ω : Type*} (Y : Ω → Θ) (X : I → Ω → Group n)
    (c d : I) (hd : d ≠ c) (ω : Ω) :
    exceptHaarColor c d (fun j => augmentedHaarVariables Y X j.val ω) = X d ω := by
  simp only [exceptHaarColor, dite_eq_right hd, exceptHaarMatrix_apply]

/-- Native selected coefficients as actual functions of the whole except-color tuple. -/
def selectedHeadDataMatrices (color : α → I) (c : I) (word : List α)
    (A : Θ → α → Matrix n n ℂ) (z : ExceptHaarData Θ I n c) :
    Fin (selectedColorSegments color c word).length → Matrix n n ℂ :=
  fun k => A (exceptHaarInputData c z) (selectedColorHead color c word k)

/-- Actual other-color run matrices as functions of the same data tuple. -/
def selectedRunDataMatrices (color : α → I) (c : I) (word : List α)
    (A : Θ → α → Matrix n n ℂ) (z : ExceptHaarData Θ I n c) :
    Fin (selectedColorSegments color c word).length → Matrix n n ℂ :=
  selectedColorRunMatrix color c word (A (exceptHaarInputData c z)) (fun d => exceptHaarColor c d z)

omit [DecidableEq n] in
private theorem measurable_matrix_mul_run {Ω : Type*} [MeasurableSpace Ω]
    (F G : Ω → Matrix n n ℂ) (hF : Measurable F) (hG : Measurable G) :
    Measurable (fun ω => F ω * G ω) := by
  apply Measurable.of_eval_matrix
  intro i j
  simp only [Matrix.mul_apply]
  apply Finset.measurable_sum
  intro k _
  exact hF.eval_matrix.mul hG.eval_matrix

/-- Actual colored matrix products are measurable from measurable input maps. -/
theorem measurable_coloredWordProduct {Ω : Type*} [MeasurableSpace Ω]
    (color : α → I) (word : List α) (A : Ω → α → Matrix n n ℂ) (U : Ω → I → Group n)
    (hA : Measurable A) (hU : Measurable U) :
    Measurable (fun ω => (word.map (coloredConjugateBlock color (A ω) (U ω))).prod) := by
  have hb (a : α) : Measurable (fun ω => coloredConjugateBlock color (A ω) (U ω) a) := by
    have hu : Measurable (fun ω => complexMatrix (U ω (color a))) := by
      apply Measurable.of_eval_matrix
      intro i j
      have he : Continuous (fun V : Group n => (V : Matrix n n ℝ) i j) :=
        (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
      exact Complex.continuous_ofReal.measurable.comp (he.measurable.comp hU.eval)
    have ht : Measurable (fun ω => (complexMatrix (U ω (color a))).transpose) := by
      apply Measurable.of_eval_matrix
      intro i j
      exact hu.eval_matrix
    exact measurable_matrix_mul_run _ _ (measurable_matrix_mul_run _ _ hu hA.eval) ht
  induction word with
  | nil => simp
  | cons a word ih =>
    simp only [List.map_cons, List.prod_cons]
    exact measurable_matrix_mul_run _ _ (hb a) ih

/-- The native selected macro-word is genuinely measurable. -/
theorem measurable_selectedHeadDataMatrices [MeasurableSpace Θ]
    (color : α → I) (c : I) (word : List α) (A : Θ → α → Matrix n n ℂ) (hA : Measurable A) :
    Measurable (selectedHeadDataMatrices color c word A) := by
  apply measurable_pi_iff.mpr
  intro k
  exact hA.eval.comp (measurable_exceptHaarInputData c)

/-- The actual run macro-word is genuinely measurable. -/
theorem measurable_selectedRunDataMatrices [MeasurableSpace Θ]
    (color : α → I) (c : I) (word : List α) (A : Θ → α → Matrix n n ℂ) (hA : Measurable A) :
    Measurable (selectedRunDataMatrices color c word A) := by
  apply measurable_pi_iff.mpr
  intro k
  exact measurable_coloredWordProduct color (selectedColorRun color c word k)
    (fun z => A (exceptHaarInputData c z)) (fun z d => exceptHaarColor c d z)
    (hA.comp (measurable_exceptHaarInputData c))
    (measurable_pi_iff.mpr (fun d => measurable_exceptHaarColor c d))

/-- Selected native coefficients recover the exact sampled original inputs. -/
theorem selectedHeadDataMatrices_apply {Ω : Type*} (color : α → I) (c : I) (word : List α)
    (A : Θ → α → Matrix n n ℂ) (Y : Ω → Θ) (X : I → Ω → Group n) (ω : Ω) :
    selectedHeadDataMatrices color c word A (fun j => augmentedHaarVariables Y X j.val ω) =
      (fun k => A (Y ω) (selectedColorHead color c word k)) := rfl

/-- Actual run data recover the exact original other-color ordered run products. -/
theorem selectedRunDataMatrices_apply {Ω : Type*} (color : α → I) (c : I) (word : List α)
    (A : Θ → α → Matrix n n ℂ) (Y : Ω → Θ) (X : I → Ω → Group n) (ω : Ω) :
    selectedRunDataMatrices color c word A (fun j => augmentedHaarVariables Y X j.val ω) =
      selectedColorRunMatrix color c word (A (Y ω)) (fun d => X d ω) := by
  funext k
  apply congrArg List.prod
  apply List.map_congr_left
  intro a ha
  have hn := selectedColorSegments_tail_colors color c word _ (List.get_mem _ k) a ha
  unfold coloredConjugateBlock
  dsimp only
  rw [exceptHaarColor_apply Y X c (color a) hn ω]
  rfl

/-- A nonempty original word gives a positive actual selected macro-word length. -/
theorem selectedColorSegments_length_pos (color : α → I) (c : I) (word : List α) (hw : word ≠ []) :
    0 < (selectedColorSegments color c word).length :=
  List.length_pos_iff_ne_nil.mpr (List.splitBy_ne_nil.mpr hw)

/-- Selected native heads are actual original word letters. -/
theorem selectedColorHead_mem (color : α → I) (c : I) (word : List α)
    (k : Fin (selectedColorSegments color c word).length) : selectedColorHead color c word k ∈ word := by
  have he : selectedColorHead color c word k ∈ (selectedColorSegments color c word).flatten :=
    List.mem_flatten.mpr ⟨_, List.get_mem _ k, List.head_mem _⟩
  rwa [selectedColorSegments_flatten] at he

/-- Run letters are actual original word letters, in their original order. -/
theorem selectedColorRun_sublist (color : α → I) (c : I) (word : List α)
    (k : Fin (selectedColorSegments color c word).length) : List.Sublist (selectedColorRun color c word k) word := by
  have he := (List.tail_sublist ((selectedColorSegments color c word).get k)).trans
    (List.sublist_flatten_of_mem (List.get_mem (selectedColorSegments color c word) k))
  rwa [selectedColorSegments_flatten] at he

/-- Every indexed actual run is strictly shorter than the original word. -/
theorem selectedColorRun_length_lt (color : α → I) (c : I) (word : List α)
    (k : Fin (selectedColorSegments color c word).length) : (selectedColorRun color c word k).length < word.length :=
  selectedColorSegments_tail_length_lt color c word _ (List.get_mem _ k)

/-- Each indexed run inherits the original adjacent alternation. -/
theorem selectedColorRun_alternating (color : α → I) (c : I) (word : List α)
    (ha : word.IsChain (fun a b => color a ≠ color b))
    (k : Fin (selectedColorSegments color c word).length) :
    (selectedColorRun color c word k).IsChain (fun a b => color a ≠ color b) :=
  selectedColorSegments_tail_alternating color c word ha _ (List.get_mem _ k)

/-- Cyclic alternation ensures positive actual run length for every indexed run. -/
theorem selectedColorRun_ne_nil (color : α → I) (c : I) (word : List α)
    (hw : word ≠ []) (hfirst : color (word.head hw) = c)
    (hlast : color (word.getLast hw) ≠ c) (ha : word.IsChain (fun a b => color a ≠ color b))
    (k : Fin (selectedColorSegments color c word).length) : selectedColorRun color c word k ≠ [] :=
  selectedColorSegments_tail_ne_nil color c word hw hfirst hlast ha _ (List.get_mem _ k)

/-- Actual run matrices inherit operator bounds from the sampled original coefficients. -/
theorem selectedRunDataMatrices_opNorm_le {Ω : Type*} (color : α → I) (c : I) (word : List α)
    (A : Θ → α → Matrix n n ℂ) (Y : Ω → Θ) (X : I → Ω → Group n) (ω : Ω)
    (K : ℝ) (hK : 0 ≤ K)
    (hA : ∀ a ∈ word, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A (Y ω) a)‖ ≤ K)
    (k : Fin (selectedColorSegments color c word).length) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
      (selectedRunDataMatrices color c word A (fun j => augmentedHaarVariables Y X j.val ω) k)‖ ≤
        (K + 1) ^ word.length := by
  rw [selectedRunDataMatrices_apply]
  have hb : ∀ a ∈ selectedColorRun color c word k,
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A (Y ω) a)‖ ≤ K + 1 := by
    intro a ha
    exact (hA a ((selectedColorRun_sublist color c word k).subset ha)).trans
      (le_add_of_nonneg_right (by positivity))
  have he := coloredWordProduct_opNorm_le color (selectedColorRun color c word k) (A (Y ω))
    (fun d => X d ω) (K + 1) (by positivity) hb
  exact he.trans (pow_le_pow_right₀ (by linarith) (selectedColorRun_length_lt color c word k).le)

end FreeProbability.Orthogonal

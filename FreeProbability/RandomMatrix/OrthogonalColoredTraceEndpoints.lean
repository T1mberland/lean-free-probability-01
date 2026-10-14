import FreeProbability.RandomMatrix.OrthogonalColoredTraceCyclicStep

/-! # Actual endpoint merger for linearly alternating colored traces -/

noncomputable section
open scoped Classical
namespace FreeProbability.Orthogonal
open Matrix MeasureTheory
variable {α I n : Type*} [Fintype n] [DecidableEq n]

/-- New endpoint slot, keeping every original native coefficient unchanged. -/
def endpointColor (color : α → I) (c : I) : α ⊕ Unit → I := Sum.elim color (fun _ => c)

/-- The merged native coefficient has the mathematically required order LAST
TIMES FIRST. Its fresh slot is centered; original slots remain unchanged. -/
def endpointCoefficients (A : α → Matrix n n ℂ) (a b : α) : α ⊕ Unit → Matrix n n ℂ :=
  Sum.elim A (fun _ => matrixTraceCenter (A b * A a))

/-- The actual shorter endpoint-merged word. -/
def endpointWord (middle : List α) : List (α ⊕ Unit) := Sum.inr () :: middle.map Sum.inl

/-- Genuine matrix conjugation respects multiplication of native coefficients. -/
theorem coloredConjugateBlock_mul_same (color : α → I) (A : α → Matrix n n ℂ)
    (U : I → Group n) (a b : α) (c : I) (ha : color a = c) (hb : color b = c) :
    coloredConjugateBlock color A U b * coloredConjugateBlock color A U a =
      complexMatrix (U c) * (A b * A a) * (complexMatrix (U c)).transpose := by
  have hu : (complexMatrix (U c)).transpose * complexMatrix (U c) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose, complexMatrix_conjTranspose] using
      Matrix.mem_unitaryGroup_iff'.mp (complexMatrix_mem_unitary (U c))
  unfold coloredConjugateBlock
  rw [ha, hb]
  calc
    _ = complexMatrix (U c) * (A b * ((complexMatrix (U c)).transpose * complexMatrix (U c)) * A a) *
        (complexMatrix (U c)).transpose := by noncomm_ring
    _ = _ := by rw [hu, mul_one]

/-- Actual cyclic trace rotation and endpoint merger produce a centered
shorter word plus the genuine scalar native trace times the interior trace. -/
theorem coloredTraceWord_endpoint_decomposition (color : α → I) (c : I)
    (a b : α) (middle : List α) (ha : color a = c) (hb : color b = c)
    (A : α → Matrix n n ℂ) (U : I → Group n) :
    coloredTraceWord color (a :: middle ++ [b]) A U =
      coloredTraceWord (endpointColor color c) (endpointWord middle) (endpointCoefficients A a b) U +
        normalizedTrace (A b * A a) * coloredTraceWord color middle A U := by
  let P := (middle.map (coloredConjugateBlock color A U)).prod
  have hrot : coloredTraceWord color (a :: middle ++ [b]) A U =
      normalizedTrace ((coloredConjugateBlock color A U b * coloredConjugateBlock color A U a) * P) := by
    unfold coloredTraceWord normalizedTrace
    simp only [List.map_cons, List.map_append, List.map_nil, List.prod_cons, List.prod_append,
      List.prod_nil, mul_one]
    rw [Matrix.trace_mul_comm _ (coloredConjugateBlock color A U b), ← Matrix.mul_assoc]
  have hc := matrixTraceCenter_orthogonal_conjugate (U c) (A b * A a)
  unfold matrixTraceCenter at hc
  rw [normalizedTrace_orthogonal_conjugate] at hc
  have he : complexMatrix (U c) * (A b * A a) * (complexMatrix (U c)).transpose =
      complexMatrix (U c) * matrixTraceCenter (A b * A a) * (complexMatrix (U c)).transpose +
        normalizedTrace (A b * A a) • (1 : Matrix n n ℂ) := sub_eq_iff_eq_add.mp hc
  have hshort : coloredTraceWord (endpointColor color c) (endpointWord middle)
      (endpointCoefficients A a b) U = normalizedTrace
        ((complexMatrix (U c) * matrixTraceCenter (A b * A a) * (complexMatrix (U c)).transpose) * P) := by
    simp only [coloredTraceWord, endpointWord, List.map_cons, List.map_map, List.prod_cons,
      endpointColor, endpointCoefficients, coloredConjugateBlock, Sum.elim_inr]
    rfl
  rw [hrot, coloredConjugateBlock_mul_same color A U a b c ha hb, he, hshort,
    add_mul, Matrix.smul_mul, one_mul]
  simp only [normalizedTrace, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
  change _ = _ + _ * ((Fintype.card n : ℂ)⁻¹ * Matrix.trace P)
  ring

/-- The native merger genuinely lowers word length. -/
theorem endpointWord_length_lt (a b : α) (middle : List α) :
    (endpointWord middle).length < (a :: middle ++ [b]).length := by
  simp only [endpointWord, List.length_cons, List.length_map, List.length_append, List.length_nil]
  omega

/-- The original interior is also genuinely shorter, with no empty-word
convergence assertion hidden in this length lemma. -/
theorem endpointInterior_length_lt (a b : α) (middle : List α) :
    middle.length < (a :: middle ++ [b]).length := by
  simp only [List.length_cons, List.length_append, List.length_nil]
  omega

/-- Actual endpoint merger preserves adjacent color alternation. -/
theorem endpointWord_alternating (color : α → I) (c : I) (a b : α) (middle : List α)
    (ha : color a = c) (hword : (a :: middle ++ [b]).IsChain (fun x y => color x ≠ color y)) :
    (endpointWord middle).IsChain (fun x y => endpointColor color c x ≠ endpointColor color c y) := by
  have he : ((a :: middle) ++ [b]).IsChain (fun x y => color x ≠ color y) := hword
  have hleft := (List.isChain_append.mp he).1
  obtain ⟨hhead, hmid⟩ := List.isChain_cons.mp hleft
  unfold endpointWord
  rw [List.isChain_cons]
  constructor
  · intro y hy
    rw [List.head?_map] at hy
    obtain ⟨x, hx, rfl⟩ := Option.mem_map.mp hy
    have hh := hhead x hx
    rw [ha] at hh
    exact hh
  · simpa only [List.isChain_map, endpointColor, Sum.elim_inl] using hmid

/-- Equal endpoint colors in an alternating word force a NONEMPTY interior;
this prevents an empty-word scalar term entering the induction. -/
theorem endpointInterior_ne_nil (color : α → I) (a b : α) (middle : List α)
    (hsame : color a = color b) (hword : (a :: middle ++ [b]).IsChain (fun x y => color x ≠ color y)) :
    middle ≠ [] := by
  intro hm
  subst middle
  exact hword.rel hsame

/-- A measurable original coefficient family gives a genuine measurable
endpoint-centered coefficient family in the fresh-slot type. -/
theorem measurable_endpointCoefficients {Θ : Type*} [MeasurableSpace Θ]
    (A : Θ → α → Matrix n n ℂ) (hA : Measurable A) (a b : α) :
    Measurable (fun θ => endpointCoefficients (A θ) a b) := by
  apply measurable_pi_iff.mpr
  intro x
  cases x with
  | inl x => exact hA.eval
  | inr _ =>
    apply (measurable_matrixTraceCenter (n := n)).comp
    apply Measurable.of_eval_matrix
    intro i j
    simp only [Matrix.mul_apply]
    apply Finset.measurable_sum
    intro k _
    exact hA.eval.eval_matrix.mul hA.eval.eval_matrix

/-- Every native factor of the actual merged word is centered. -/
theorem endpointCoefficients_trace (A : α → Matrix n n ℂ) (a b : α) (middle : List α)
    (hA : ∀ x ∈ middle, Matrix.trace (A x) = 0) :
    ∀ x ∈ endpointWord middle, Matrix.trace (endpointCoefficients A a b x) = 0 := by
  intro x hx
  cases x with
  | inl x =>
    have hm : x ∈ middle := by simpa only [endpointWord, List.mem_cons, List.mem_map, Sum.inl.injEq,
      Sum.inl_ne_inr, false_or, exists_eq_right] using hx
    exact hA x hm
  | inr _ => exact matrixTraceCenter_trace _

/-- Genuine endpoint native bounds are inherited from the actual original
operator norms, with a uniform bound allowing the new centered product. -/
theorem endpointCoefficients_opNorm_le (A : α → Matrix n n ℂ) (a b : α) (middle : List α)
    (K : ℝ) (hK : 0 ≤ K)
    (ha : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A a)‖ ≤ K)
    (hb : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A b)‖ ≤ K)
    (hA : ∀ x ∈ middle, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A x)‖ ≤ K) :
    ∀ x ∈ endpointWord middle, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (endpointCoefficients A a b x)‖ ≤ K + 2 * K ^ 2 := by
  have hp : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A b * A a)‖ ≤ K ^ 2 := by
    rw [map_mul]
    exact (norm_mul_le _ _).trans (by simpa only [pow_two] using mul_le_mul hb ha (norm_nonneg _) hK)
  intro x hx
  cases x with
  | inl x =>
    have hm : x ∈ middle := by simpa only [endpointWord, List.mem_cons, List.mem_map, Sum.inl.injEq,
      Sum.inl_ne_inr, false_or, exists_eq_right] using hx
    exact (hA x hm).trans (by nlinarith [sq_nonneg K])
  | inr _ =>
    exact ((matrixTraceCenter_opNorm_le _).trans (mul_le_mul_of_nonneg_left hp (by positivity))).trans
      (by linarith)

end FreeProbability.Orthogonal

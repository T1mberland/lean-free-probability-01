import FreeProbability.RandomMatrix.OrthogonalMultiTraceProbability
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Analysis.Matrix.MeasurableSpace

/-! # Actual pointwise bounds for independently sampled matrix inputs -/

noncomputable section
open scoped Classical
namespace FreeProbability.Orthogonal
open Matrix MeasureTheory
variable {n : Type*} [Fintype n] [DecidableEq n]

section NormBounds
open scoped Matrix.Norms.L2Operator

/-- Complexification of an actual real orthogonal matrix is genuinely unitary. -/
theorem complexMatrix_mem_unitary (U : Group n) :
    complexMatrix U ∈ Matrix.unitaryGroup n ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  rw [Matrix.star_eq_conjTranspose, complexMatrix_conjTranspose]
  change ((U : Matrix n n ℝ).map (Complex.ofRealHom : ℝ →+* ℂ)) *
    ((U : Matrix n n ℝ).transpose.map (Complex.ofRealHom : ℝ →+* ℂ)) = 1
  rw [← Matrix.map_mul, (Matrix.mem_orthogonalGroup_iff n ℝ).mp U.property]
  simp

/-- Genuine normalized trace is contractive for the Euclidean operator norm,
including dimension zero with the project's zero normalization. -/
theorem normalizedTrace_norm_le_Euclidean_opNorm (M : Matrix n n ℂ) :
    ‖normalizedTrace M‖ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) M‖ := by
  by_cases hn : Fintype.card n = 0
  · simp [normalizedTrace, hn]
  · have hNr : (0 : ℝ) < Fintype.card n := by exact_mod_cast Nat.pos_of_ne_zero hn
    unfold normalizedTrace
    rw [norm_mul]
    have hni : ‖(Fintype.card n : ℂ)⁻¹‖ = (Fintype.card n : ℝ)⁻¹ := by simp
    rw [hni]
    calc
      _ ≤ (Fintype.card n : ℝ)⁻¹ * ((Fintype.card n : ℝ) *
          ‖Matrix.toEuclideanCLM (𝕜 := ℂ) M‖) :=
        mul_le_mul_of_nonneg_left (trace_norm_le_card_mul_Euclidean_opNorm M) (by positivity)
      _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hNr.ne', one_mul]

/-- Unitary Haar conjugation gives the actual two-factor operator bound. -/
theorem traceWord_block_opNorm_le (U : Group n) (A B : Matrix n n ℂ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (complexMatrix U * A * (complexMatrix U).transpose * B)‖ ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) B‖ := by
  have hu := complexMatrix_mem_unitary U
  have ht := Matrix.transpose_mem_unitaryGroup_iff.mpr hu
  have hb := norm_mul_le (complexMatrix U * A * (complexMatrix U).transpose) B
  rw [CStarRing.norm_mul_mem_unitary _ ht, CStarRing.norm_mem_unitary_mul _ hu] at hb
  simpa only [Matrix.cstar_norm_def] using hb

/-- A true pointwise trace-word bound, requiring no centering or Haar integration. -/
theorem traceWord_norm_le_product {r : ℕ} (hr : 0 < r)
    (A B : Fin r → Matrix n n ℂ) (U : Group n) :
    ‖traceWord A B U‖ ≤ (∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A k)‖) *
      (∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B k)‖) := by
  have hne : List.ofFn (fun k => complexMatrix U * A k * (complexMatrix U).transpose * B k) ≠ [] := by
    intro h
    have he := congrArg List.length h
    simp only [List.length_ofFn, List.length_nil] at he
    omega
  apply (normalizedTrace_norm_le_Euclidean_opNorm _).trans
  have hp := List.norm_prod_le' hne
  have hp' : ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
      (List.ofFn (fun k => complexMatrix U * A k * (complexMatrix U).transpose * B k)).prod‖ ≤
      ∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
        (complexMatrix U * A k * (complexMatrix U).transpose * B k)‖ := by
    simpa only [List.map_ofFn, List.prod_ofFn, Function.comp_def, Matrix.cstar_norm_def] using hp
  exact hp'.trans (by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀ (fun k _ => norm_nonneg _) (fun k _ => traceWord_block_opNorm_le U _ _))

/-- A global operator bound gives a true global scalar bound in every dimension. -/
theorem traceWord_norm_le_uniform {r : ℕ} (hr : 0 < r) (K : ℝ) (hK : 0 ≤ K)
    (A B : Fin r → Matrix n n ℂ) (U : Group n)
    (hA : ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A k)‖ ≤ K)
    (hB : ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B k)‖ ≤ K) :
    ‖traceWord A B U‖ ≤ K ^ (2 * r) := by
  have ha : (∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A k)‖) ≤ K ^ r := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      Finset.prod_le_prod₀ (s := Finset.univ) (fun k _ => norm_nonneg _) (fun k _ => hA k)
  have hb : (∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B k)‖) ≤ K ^ r := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      Finset.prod_le_prod₀ (s := Finset.univ) (fun k _ => norm_nonneg _) (fun k _ => hB k)
  apply (traceWord_norm_le_product hr A B U).trans
  calc
    _ ≤ K ^ r * K ^ r := mul_le_mul ha hb (Finset.prod_nonneg (fun k _ => norm_nonneg _)) (by positivity)
    _ = _ := by rw [two_mul, pow_add]

end NormBounds

/-- The actual trace polynomial is jointly continuous in both entire matrix
words and the actual orthogonal matrix. -/
theorem continuous_traceWord_inputs {r : ℕ} :
    Continuous (fun z : (Fin r → Matrix n n ℂ) × (Fin r → Matrix n n ℂ) × Group n =>
      traceWord z.1 z.2.1 z.2.2) := by
  have hcU : Continuous (complexMatrix : Group n → Matrix n n ℂ) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    have he : Continuous (fun U : Group n => (U : Matrix n n ℝ) i j) :=
      (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
    exact Complex.continuous_ofReal.comp he
  have hU : Continuous (fun z : (Fin r → Matrix n n ℂ) × (Fin r → Matrix n n ℂ) × Group n =>
      complexMatrix z.2.2) := hcU.comp (continuous_snd.comp continuous_snd)
  have hp : Continuous (fun z : (Fin r → Matrix n n ℂ) × (Fin r → Matrix n n ℂ) × Group n =>
      (List.ofFn (fun k => complexMatrix z.2.2 * z.1 k * (complexMatrix z.2.2).transpose * z.2.1 k)).prod) := by
    simp_rw [List.ofFn_eq_map]
    apply continuous_list_prod
    intro k _
    exact ((hU.mul ((continuous_apply k).comp continuous_fst)).mul hU.matrix_transpose).mul
      ((continuous_apply k).comp (continuous_fst.comp continuous_snd))
  unfold traceWord normalizedTrace
  apply continuous_const.mul
  unfold Matrix.trace
  apply continuous_finsetSum
  intro i _
  exact (continuous_apply i).comp ((continuous_apply i).comp hp)

omit [DecidableEq n] in
private theorem measurable_matrix_mul {Ω : Type*} [MeasurableSpace Ω]
    (F G : Ω → Matrix n n ℂ) (hF : Measurable F) (hG : Measurable G) :
    Measurable (fun ω => F ω * G ω) := by
  apply Measurable.of_eval_matrix
  intro i j
  simp only [Matrix.mul_apply]
  apply Finset.measurable_sum
  intro k _
  exact hF.eval_matrix.mul hG.eval_matrix

private theorem measurable_ordered_matrix_product {Ω : Type*} [MeasurableSpace Ω]
    (r : ℕ) (M : Fin r → Ω → Matrix n n ℂ) (hM : ∀ k, Measurable (M k)) :
    Measurable (fun ω => (List.ofFn (fun k => M k ω)).prod) := by
  induction r with
  | zero => simp
  | succ r ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    exact measurable_matrix_mul _ _ (hM 0) (ih (fun k => M k.succ) (fun k => hM k.succ))

/-- Measurable random inputs give a genuinely measurable trace observable. -/
theorem measurable_traceWord_inputs {Ω : Type*} [MeasurableSpace Ω] {r : ℕ}
    (A B : Ω → Fin r → Matrix n n ℂ) (X : Ω → Group n)
    (hA : Measurable A) (hB : Measurable B) (hX : Measurable X) :
    Measurable (fun ω => traceWord (A ω) (B ω) (X ω)) := by
  have hU : Measurable (fun ω => complexMatrix (X ω)) := by
    apply Measurable.of_eval_matrix
    intro i j
    have he : Continuous (fun U : Group n => (U : Matrix n n ℝ) i j) :=
      (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
    exact Complex.continuous_ofReal.measurable.comp (he.measurable.comp hX)
  have ht : Measurable (fun ω => (complexMatrix (X ω)).transpose) := by
    apply Measurable.of_eval_matrix
    intro i j
    exact hU.eval_matrix
  have hp := measurable_ordered_matrix_product r (fun k ω =>
    complexMatrix (X ω) * A ω k * (complexMatrix (X ω)).transpose * B ω k) (fun k =>
      measurable_matrix_mul _ _ (measurable_matrix_mul _ _
        (measurable_matrix_mul _ _ hU (hA.eval)) ht) (hB.eval))
  unfold traceWord normalizedTrace
  apply measurable_const.mul
  unfold Matrix.trace
  apply Finset.measurable_sum
  intro i _
  exact hp.eval_matrix

end FreeProbability.Orthogonal

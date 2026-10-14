import FreeProbability.RandomMatrix.OrthogonalColoredEntrySites

/-! # Actual normalized trace centering for colored trace words -/

noncomputable section
open scoped Classical Topology
namespace FreeProbability.Orthogonal
open Matrix MeasureTheory
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Actual normalized trace centering of a finite complex matrix. -/
def matrixTraceCenter (A : Matrix n n ℂ) : Matrix n n ℂ :=
  A - normalizedTrace A • 1

/-- Actual centering has zero ordinary trace, including empty matrix dimension. -/
theorem matrixTraceCenter_trace (A : Matrix n n ℂ) : Matrix.trace (matrixTraceCenter A) = 0 := by
  by_cases hn : Fintype.card n = 0
  · let : IsEmpty n := Fintype.card_eq_zero_iff.mp hn
    simp [Matrix.trace]
  · have hNc : (Fintype.card n : ℂ) ≠ 0 := by exact_mod_cast hn
    unfold matrixTraceCenter normalizedTrace
    rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
    field_simp
    ring

/-- The uncentered part is EXACTLY the original normalized trace times identity. -/
theorem sub_matrixTraceCenter (A : Matrix n n ℂ) :
    A - matrixTraceCenter A = normalizedTrace A • 1 := by
  unfold matrixTraceCenter
  abel

/-- The actual identity operator has norm at most one even in dimension zero. -/
theorem Euclidean_opNorm_one_le :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (1 : Matrix n n ℂ)‖ ≤ 1 := by
  have h1 : Matrix.toEuclideanCLM (𝕜 := ℂ) (1 : Matrix n n ℂ) =
      (1 : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) := map_one _
  rw [h1]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  simp

/-- Actual matrix centering costs at most twice the genuine Euclidean operator norm. -/
theorem matrixTraceCenter_opNorm_le (A : Matrix n n ℂ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (matrixTraceCenter A)‖ ≤
      2 * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ := by
  open scoped Matrix.Norms.L2Operator in
    have hi : ‖(1 : Matrix n n ℂ)‖ ≤ 1 := by
      simpa only [Matrix.cstar_norm_def] using (Euclidean_opNorm_one_le (n := n))
    have hs : ‖normalizedTrace A • (1 : Matrix n n ℂ)‖ ≤ ‖normalizedTrace A‖ := by
      rw [norm_smul]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hi (norm_nonneg (normalizedTrace A))
    have hb := (norm_sub_le A (normalizedTrace A • (1 : Matrix n n ℂ))).trans
      (add_le_add_right hs ‖A‖)
    have hn : ‖normalizedTrace A‖ ≤ ‖A‖ := by
      simpa only [Matrix.cstar_norm_def] using normalizedTrace_norm_le_Euclidean_opNorm A
    have hfin := hb.trans (add_le_add_right hn ‖A‖)
    simpa only [matrixTraceCenter, Matrix.cstar_norm_def, two_mul] using hfin

/-- The difference from the centered matrix is bounded by its actual normalized trace. -/
theorem sub_matrixTraceCenter_opNorm_le (A : Matrix n n ℂ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A - matrixTraceCenter A)‖ ≤ ‖normalizedTrace A‖ := by
  rw [sub_matrixTraceCenter, map_smul, norm_smul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (Euclidean_opNorm_one_le (n := n))
    (norm_nonneg (normalizedTrace A))

/-- Centering is an actual continuous matrix operation. -/
theorem continuous_matrixTraceCenter : Continuous (matrixTraceCenter : Matrix n n ℂ → Matrix n n ℂ) := by
  have ht : Continuous (normalizedTrace : Matrix n n ℂ → ℂ) := by
    unfold normalizedTrace Matrix.trace
    apply continuous_const.mul
    apply continuous_finsetSum
    intro i _
    exact (continuous_apply i).comp (continuous_apply i)
  exact continuous_id.sub (ht.smul continuous_const)

/-- Measurable random matrix inputs remain genuinely measurable when centered. -/
theorem measurable_matrixTraceCenter : Measurable (matrixTraceCenter : Matrix n n ℂ → Matrix n n ℂ) :=
  continuous_matrixTraceCenter.measurable

/-- Actual orthogonal conjugation preserves the normalized matrix trace. -/
theorem normalizedTrace_orthogonal_conjugate (U : Group n) (A : Matrix n n ℂ) :
    normalizedTrace (complexMatrix U * A * (complexMatrix U).transpose) = normalizedTrace A := by
  have hu : (complexMatrix U).transpose * complexMatrix U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose, complexMatrix_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff'.mp (complexMatrix_mem_unitary U))
  unfold normalizedTrace
  rw [Matrix.trace_mul_comm (complexMatrix U * A) (complexMatrix U).transpose,
    ← Matrix.mul_assoc, hu, one_mul]

/-- Actual normalized-trace centering commutes with orthogonal conjugation. -/
theorem matrixTraceCenter_orthogonal_conjugate (U : Group n) (A : Matrix n n ℂ) :
    matrixTraceCenter (complexMatrix U * A * (complexMatrix U).transpose) =
      complexMatrix U * matrixTraceCenter A * (complexMatrix U).transpose := by
  have hu : complexMatrix U * (complexMatrix U).transpose = 1 := by
    simpa only [Matrix.star_eq_conjTranspose, complexMatrix_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff.mp (complexMatrix_mem_unitary U))
  unfold matrixTraceCenter
  rw [normalizedTrace_orthogonal_conjugate]
  simp only [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, mul_one, hu]

end FreeProbability.Orthogonal

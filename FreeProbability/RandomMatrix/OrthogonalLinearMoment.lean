import FreeProbability.RandomMatrix.OrthogonalQuadraticMoment

/-! # Linear forms and their exact fourth Haar moments -/

namespace FreeProbability.Orthogonal

open Matrix MeasureTheory

variable {n : Type*} [Fintype n] [DecidableEq n]

def rowLinearForm (a : n → ℝ) (r : n) (U : Group n) : ℝ :=
  (fun i => U r i) ⬝ᵥ a

theorem rowQuadraticForm_outer (a : n → ℝ) (r : n) (U : Group n) :
    rowQuadraticForm (vecMulVec a a) r U = rowLinearForm a r U ^ 2 := by
  simp [rowQuadraticForm, rowLinearForm, Matrix.vecMulVec_mulVec, dotProduct_smul,
    dotProduct_comm, pow_two]

theorem integral_rowLinearForm_pow_four (a : n → ℝ) (r : n) :
    (∫ U : Group n, rowLinearForm a r U ^ 4 ∂haar n) =
      3 * (a ⬝ᵥ a) ^ 2 / ((Fintype.card n : ℝ) * ((Fintype.card n : ℝ) + 2)) := by
  have he (U : Group n) : rowLinearForm a r U ^ 4 = rowQuadraticForm (vecMulVec a a) r U ^ 2 := by
    rw [rowQuadraticForm_outer]
    ring
  simp_rw [he]
  have hs : (vecMulVec a a)ᵀ = vecMulVec a a := by
    ext i j
    simp [vecMulVec_apply, mul_comm]
  rw [integral_rowQuadraticForm_sq_of_symmetric _ r hs, Matrix.trace_vecMulVec,
    Matrix.vecMulVec_mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_smul]
  congr 1
  simp [smul_eq_mul]
  ring

omit [DecidableEq n] in
theorem real_dotProduct_self_eq_norm_sq (a : n → ℝ) :
    a ⬝ᵥ a = ‖WithLp.toLp 2 a‖ ^ 2 := by
  simpa [dotProduct, pow_two] using (EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 a)).symm

theorem integral_rowLinearForm_pow_four_norm (a : n → ℝ) (r : n) :
    (∫ U : Group n, rowLinearForm a r U ^ 4 ∂haar n) =
      3 * ‖WithLp.toLp 2 a‖ ^ 4 / ((Fintype.card n : ℝ) * ((Fintype.card n : ℝ) + 2)) := by
  rw [integral_rowLinearForm_pow_four, real_dotProduct_self_eq_norm_sq]
  congr 1
  ring

end FreeProbability.Orthogonal

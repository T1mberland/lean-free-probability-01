import FreeProbability.OperatorValued.MatrixSemicircularModel
import FreeProbability.Fock.WordIntegrationByParts

/-! # Actual matrix vacuum boundary calculus

The boundary commutator and rank-one contraction hold for arbitrary matrices
of bounded Fock operators, hence also for genuine inverse operators.
-/

noncomputable section
open scoped Classical
namespace FreeProbability.Fock

variable {I n : Type*} [Fintype n] [DecidableEq n]

/-- The amplified right annihilation boundary operator. -/
def matrixRightAnnihilation (i : I) : Matrix n n (WordSpace I →L[ℂ] WordSpace I) :=
  Matrix.diagonal (fun _ => rightAnnihilation i)

/-- Vacuum contraction of the amplified boundary commutator. -/
theorem matrixVacuumExpectation_rightAnnihilation_commutator (i : I)
    (T : Matrix n n (WordSpace I →L[ℂ] WordSpace I)) :
    matrixExpectation (vacuumState I).toProbabilitySpace
      (matrixRightAnnihilation i * T - T * matrixRightAnnihilation i) =
      matrixExpectation (vacuumState I).toProbabilitySpace
        (Matrix.diagonal (fun _ : n => semicircular i) * T) := by
  ext r c
  simp only [matrixExpectation_apply, matrixRightAnnihilation, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  exact vacuumExpectation_rightAnnihilation_commutator i (T r c)

private theorem vacuumExpectation_coefficient_projection (c : ℂ)
    (T S : WordSpace I →L[ℂ] WordSpace I) :
    vacuumExpectation (T * algebraMap ℂ _ c * vacuumProjection * S) =
      vacuumExpectation T * c * vacuumExpectation S := by
  rw [← Algebra.commutes c T, mul_assoc, ← Algebra.smul_def]
  change (vacuumState I).expectation (c • (T * vacuumProjection * S)) = _
  rw [map_smul]
  change c * vacuumExpectation (T * vacuumProjection * S) = _
  rw [vacuumExpectation_mul_vacuumProjection_mul]
  ac_rfl

/-- Exact rank-one contraction with an arbitrary deterministic coefficient
matrix in the middle; all matrix multiplication orders are preserved. -/
theorem matrixVacuumExpectation_mul_projection_mul
    (T S : Matrix n n (WordSpace I →L[ℂ] WordSpace I)) (C : Matrix n n ℂ) :
    matrixExpectation (vacuumState I).toProbabilitySpace
      (T * scalarMatrixEmbedding C * Matrix.diagonal (fun _ : n => vacuumProjection) * S) =
      matrixExpectation (vacuumState I).toProbabilitySpace T * C *
        matrixExpectation (vacuumState I).toProbabilitySpace S := by
  ext r c
  simp only [matrixExpectation_apply]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    scalarMatrixEmbedding_apply, Finset.sum_mul, map_sum]
  change (∑ v, ∑ u, vacuumExpectation (T r u * algebraMap ℂ _ (C u v) * vacuumProjection * S v c)) = _
  simp only [vacuumExpectation_coefficient_projection,
    matrixExpectation_apply]
  rfl

variable [Fintype I]

/-- Actual boundary derivative of the matrix semicircular linear combination. -/
theorem matrixRightAnnihilation_linearCombination_commutator (i : I) (C : I → Matrix n n ℂ) :
    matrixRightAnnihilation i * matrixLinearCombination semicircular C -
      matrixLinearCombination semicircular C * matrixRightAnnihilation i =
      scalarMatrixEmbedding (C i) * Matrix.diagonal (fun _ : n => vacuumProjection) := by
  ext r c
  simp only [matrixRightAnnihilation, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    matrixLinearCombination, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    ← Finset.sum_sub_distrib, ← smul_sub, rightAnnihilation_semicircular_commutator,
    smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    scalarMatrixEmbedding_apply]
  rfl

end FreeProbability.Fock

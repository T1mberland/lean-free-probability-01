import FreeProbability.OperatorValued.MatrixLinearCombination
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators

/-! # Ordered matrix word expansions with arbitrary scalar coefficient arrays -/

namespace FreeProbability

open Matrix

variable {A n I : Type*} [Ring A] [Algebra ℂ A] [Fintype n] [DecidableEq n] [Fintype I]

private theorem diagonal_commutes_scalarMatrix (x : A) (C : Matrix n n ℂ) :
    Matrix.diagonal (fun _ : n => x) * scalarMatrixEmbedding C =
      scalarMatrixEmbedding C * Matrix.diagonal (fun _ : n => x) := by
  ext r c
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  exact (Algebra.commutes (C r c) x).symm

private theorem coefficient_diagonal_mul (C D : Matrix n n ℂ) (x y : A) :
    (scalarMatrixEmbedding C * Matrix.diagonal (fun _ : n => x)) *
      (scalarMatrixEmbedding D * Matrix.diagonal (fun _ : n => y)) =
        scalarMatrixEmbedding (C * D) * Matrix.diagonal (fun _ : n => x * y) := by
  calc
    _ = scalarMatrixEmbedding C * (Matrix.diagonal (fun _ : n => x) * scalarMatrixEmbedding D) *
        Matrix.diagonal (fun _ : n => y) := by simp only [mul_assoc]
    _ = scalarMatrixEmbedding C * (scalarMatrixEmbedding D * Matrix.diagonal (fun _ : n => x)) *
        Matrix.diagonal (fun _ : n => y) := by rw [diagonal_commutes_scalarMatrix]
    _ = (scalarMatrixEmbedding C * scalarMatrixEmbedding D) *
        (Matrix.diagonal (fun _ : n => x) * Matrix.diagonal (fun _ : n => y)) := by simp only [mul_assoc]
    _ = _ := by rw [← map_mul, Matrix.diagonal_mul_diagonal]


/-- Arbitrary deterministic matrix coefficients on the right are absorbed into
the actual coefficient array, preserving their order. -/
theorem matrixLinearCombination_mul_scalarMatrix (s : I → A) (C : I → Matrix n n ℂ)
    (D : Matrix n n ℂ) :
    matrixLinearCombination s C * scalarMatrixEmbedding D =
      matrixLinearCombination s (fun i => C i * D) := by
  rw [matrixLinearCombination_eq_sum, matrixLinearCombination_eq_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = scalarMatrixEmbedding (C i) *
        (Matrix.diagonal (fun _ : n => s i) * scalarMatrixEmbedding D) := mul_assoc _ _ _
    _ = scalarMatrixEmbedding (C i) *
        (scalarMatrixEmbedding D * Matrix.diagonal (fun _ : n => s i)) := by
      rw [diagonal_commutes_scalarMatrix]
    _ = _ := by rw [← mul_assoc, ← map_mul]

/-- The corresponding left coefficient absorption also preserves matrix order. -/
theorem scalarMatrix_mul_matrixLinearCombination (s : I → A) (C : I → Matrix n n ℂ)
    (D : Matrix n n ℂ) :
    scalarMatrixEmbedding D * matrixLinearCombination s C =
      matrixLinearCombination s (fun i => D * C i) := by
  rw [matrixLinearCombination_eq_sum, matrixLinearCombination_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← mul_assoc, ← map_mul]

/-- Expansion of an actual product of coordinate-dependent matrix linear
combinations into all color assignments, with both word orders preserved. -/
theorem matrixLinearCombination_word_expansion (s : I → A) {k : ℕ}
    (C : Fin k → I → Matrix n n ℂ) :
    (List.ofFn (fun j => matrixLinearCombination s (C j))).prod =
      ∑ f : Fin k → I,
        scalarMatrixEmbedding (List.ofFn (fun j => C j (f j))).prod *
          Matrix.diagonal (fun _ : n => (List.ofFn (fun j => s (f j))).prod) := by
  classical
  induction k with
  | zero => simp [Matrix.diagonal_one]
  | succ k ih =>
    rw [List.ofFn_succ, List.prod_cons, ih]
    rw [matrixLinearCombination_eq_sum, Finset.sum_mul]
    simp_rw [Finset.mul_sum, coefficient_diagonal_mul]
    trans ∑ z : I × (Fin k → I),
      scalarMatrixEmbedding (C 0 z.1 * (List.ofFn (fun j => C j.succ (z.2 j))).prod) *
        Matrix.diagonal (fun _ : n => s z.1 * (List.ofFn (fun j => s (z.2 j))).prod)
    · exact (Fintype.sum_prod_type (fun z : I × (Fin k → I) =>
        scalarMatrixEmbedding (C 0 z.1 * (List.ofFn (fun j => C j.succ (z.2 j))).prod) *
          Matrix.diagonal (fun _ : n => s z.1 * (List.ofFn (fun j => s (z.2 j))).prod))).symm
    · apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (k + 1) => I))
      intro z
      simp only [List.ofFn_succ, List.prod_cons, Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero, Fin.cons_succ]

/-- Expectation of a literal coefficient matrix times a scalar diagonal variable. -/
theorem matrixExpectation_coefficient_diagonal (φ : ProbabilitySpace ℂ A)
    (C : Matrix n n ℂ) (x : A) :
    matrixExpectation φ (scalarMatrixEmbedding C * Matrix.diagonal (fun _ : n => x)) =
      φ.expectation x • C := by
  ext r c
  rw [matrixExpectation_apply, Matrix.mul_diagonal]
  change φ.expectation (algebraMap ℂ A (C r c) * x) = φ.expectation x * C r c
  rw [← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

/-- Matrix-valued word moments are the exact ordered coefficient-word products
weighted by scalar joint moments, with no independence assumption. -/
theorem matrixExpectation_word_expansion (φ : ProbabilitySpace ℂ A) (s : I → A) {k : ℕ}
    (C : Fin k → I → Matrix n n ℂ) :
    matrixExpectation φ (List.ofFn (fun j => matrixLinearCombination s (C j))).prod =
      ∑ f : Fin k → I, φ.expectation (List.ofFn (fun j => s (f j))).prod •
        (List.ofFn (fun j => C j (f j))).prod := by
  rw [matrixLinearCombination_word_expansion, map_sum]
  apply Finset.sum_congr rfl
  intro f _
  exact matrixExpectation_coefficient_diagonal _ _ _

end FreeProbability

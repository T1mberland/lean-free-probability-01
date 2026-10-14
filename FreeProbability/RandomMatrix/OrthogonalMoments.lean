import FreeProbability.RandomMatrix.OrthogonalHaar

/-! # Orthogonal Haar moments under coordinate reflections -/

namespace FreeProbability.Orthogonal

open Matrix MeasureTheory

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The diagonal orthogonal matrix reflecting a single coordinate. -/
def coordinateReflection (r : n) : Group n :=
  ⟨Matrix.diagonal (fun x => if x = r then (-1 : ℝ) else 1), by
    apply (Matrix.mem_orthogonalGroup_iff n ℝ).mpr
    rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
    ext i j
    simp only [Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs <;> simp_all⟩

theorem coordinateReflection_mul_apply (r : n) (U : Group n) (i j : n) :
    (coordinateReflection r * U) i j = (if i = r then -1 else 1) * U i j := by
  change (Matrix.diagonal (fun x => if x = r then (-1 : ℝ) else 1) * (U : Matrix n n ℝ)) i j = _
  rw [Matrix.diagonal_mul]

theorem mul_coordinateReflection_apply (r : n) (U : Group n) (i j : n) :
    (U * coordinateReflection r) i j = U i j * (if j = r then -1 else 1) := by
  change ((U : Matrix n n ℝ) * Matrix.diagonal (fun x => if x = r then (-1 : ℝ) else 1)) i j = _
  rw [Matrix.mul_diagonal]

theorem entryMonomial_reflection {k : ℕ} (i j : Fin k → n) (r : n) (U : Group n) :
    entryMonomial i j (coordinateReflection r * U) =
      (-1 : ℝ) ^ (Finset.univ.filter (fun a => i a = r)).card * entryMonomial i j U := by
  unfold entryMonomial
  simp only [coordinateReflection_mul_apply]
  rw [Finset.prod_mul_distrib]
  congr 1
  simp [Finset.prod_ite]

/-- A row appearing an odd number of times makes the Haar entry moment zero.
This is an all-order coordinate parity constraint, not just odd total degree. -/
theorem entryMoment_eq_zero_of_odd_row_count {k : ℕ} (i j : Fin k → n) (r : n)
    (hr : Odd (Finset.univ.filter (fun a => i a = r)).card) : entryMoment i j = 0 := by
  have heq := integral_mul_left_eq_self (μ := haar n) (entryMonomial i j) (coordinateReflection r)
  have hneg : ∀ U : Group n, entryMonomial i j (coordinateReflection r * U) = -entryMonomial i j U := by
    intro U
    rw [entryMonomial_reflection, hr.neg_one_pow, neg_one_mul]
  simp_rw [hneg] at heq
  rw [integral_neg] at heq
  change -entryMoment i j = entryMoment i j at heq
  linarith

theorem entryMonomial_inv {k : ℕ} (i j : Fin k → n) (U : Group n) :
    entryMonomial i j U⁻¹ = entryMonomial j i U := by
  simp [entryMonomial, Matrix.star_apply]

theorem integral_entry_eq_zero (r c : n) : (∫ U : Group n, U r c ∂haar n) = 0 := by
  have h := entryMoment_eq_zero_of_odd (fun _ : Fin 1 => r) (fun _ : Fin 1 => c) (by decide)
  simpa [entryMoment, entryMonomial] using h

/-- Transposition swaps the row and column words without changing the Haar moment. -/
theorem entryMoment_swap {k : ℕ} (i j : Fin k → n) : entryMoment i j = entryMoment j i := by
  have h := integral_inv_eq_self (entryMonomial i j) (haar n)
  simp only [entryMonomial_inv] at h
  exact h.symm

theorem entryMoment_eq_zero_of_odd_column_count {k : ℕ} (i j : Fin k → n) (r : n)
    (hr : Odd (Finset.univ.filter (fun a => j a = r)).card) : entryMoment i j = 0 := by
  rw [entryMoment_swap]
  exact entryMoment_eq_zero_of_odd_row_count j i r hr

end FreeProbability.Orthogonal

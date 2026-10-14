import FreeProbability.RandomMatrix.OrthogonalMoments
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic.FinCases

/-! # Exact covariance of real orthogonal Haar matrix entries -/

namespace FreeProbability.Orthogonal

open Matrix MeasureTheory

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An orthogonal permutation matrix. -/
def permutation (σ : Equiv.Perm n) : Group n :=
  ⟨σ.permMatrix ℝ, by
    apply (Matrix.mem_orthogonalGroup_iff n ℝ).mpr
    rw [Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul]
    simp⟩

theorem mul_permutation_apply (U : Group n) (σ : Equiv.Perm n) (i j : n) :
    (U * permutation σ) i j = U i (σ.symm j) := by
  change ((U : Matrix n n ℝ) * (σ.permMatrix ℝ : Matrix n n ℝ)) i j = _
  rw [PEquiv.mul_toMatrix_toPEquiv]
  rfl

theorem integral_entry_sq_eq (r c d : n) :
    (∫ U : Group n, (U r c) ^ 2 ∂haar n) = ∫ U : Group n, (U r d) ^ 2 ∂haar n := by
  have h := integral_mul_right_eq_self (μ := haar n)
    (fun U : Group n => (U r c) ^ 2) (permutation (Equiv.swap c d))
  simp only [mul_permutation_apply, Equiv.symm_swap, Equiv.swap_apply_left] at h
  exact h.symm

/-- Every Haar orthogonal entry has variance the reciprocal dimension. -/
theorem integral_entry_sq (r c : n) :
    (∫ U : Group n, (U r c) ^ 2 ∂haar n) = (Fintype.card n : ℝ)⁻¹ := by
  have hi (j : n) : Integrable (fun U : Group n => (U r j) ^ 2) (haar n) := by
    convert integrable_entryMonomial (fun _ : Fin 2 => r) (fun _ : Fin 2 => j) using 1
    funext U
    simp [entryMonomial, pow_two]
  have hs : (∑ j, ∫ U : Group n, (U r j) ^ 2 ∂haar n) = 1 := by
    rw [← integral_finsetSum Finset.univ (fun j _ => hi j)]
    simp_rw [sum_row_sq]
    simp
  simp_rw [integral_entry_sq_eq r _ c] at hs
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  have hd : (Fintype.card n : ℝ) ≠ 0 := by
    let _ : Nonempty n := ⟨r⟩
    exact_mod_cast Fintype.card_ne_zero
  rw [← one_div]
  exact (eq_div_iff hd).mpr (by simpa [mul_comm] using hs)

theorem integral_entry_mul_eq_zero_of_row_ne (r s c d : n) (hrs : r ≠ s) :
    (∫ U : Group n, U r c * U s d ∂haar n) = 0 := by
  let i : Fin 2 → n := fun a => if a = 0 then r else s
  let j : Fin 2 → n := fun a => if a = 0 then c else d
  have hodd : Odd (Finset.univ.filter (fun a : Fin 2 => i a = r)).card := by
    have hf : (Finset.univ.filter (fun a : Fin 2 => i a = r)) = {0} := by
      ext a
      fin_cases a <;> simp [i, hrs.symm]
    rw [hf]
    simp
  have h := entryMoment_eq_zero_of_odd_row_count i j r hodd
  simpa [entryMoment, entryMonomial, i, j, Fin.prod_univ_succ] using h

theorem integral_entry_mul_eq_zero_of_column_ne (r s c d : n) (hcd : c ≠ d) :
    (∫ U : Group n, U r c * U s d ∂haar n) = 0 := by
  let i : Fin 2 → n := fun a => if a = 0 then r else s
  let j : Fin 2 → n := fun a => if a = 0 then c else d
  have hodd : Odd (Finset.univ.filter (fun a : Fin 2 => j a = c)).card := by
    have hf : (Finset.univ.filter (fun a : Fin 2 => j a = c)) = {0} := by
      ext a
      fin_cases a <;> simp [j, hcd.symm]
    rw [hf]
    simp
  have h := entryMoment_eq_zero_of_odd_column_count i j c hodd
  simpa [entryMoment, entryMonomial, i, j, Fin.prod_univ_succ] using h

/-- The complete second-entry moment: Kronecker deltas divided by the dimension. -/
theorem integral_entry_mul (r s c d : n) :
    (∫ U : Group n, U r c * U s d ∂haar n) =
      if r = s ∧ c = d then (Fintype.card n : ℝ)⁻¹ else 0 := by
  by_cases hrs : r = s
  · subst s
    by_cases hcd : c = d
    · subst d
      simpa [pow_two] using integral_entry_sq r c
    · simp [hcd, integral_entry_mul_eq_zero_of_column_ne r r c d hcd]
  · simp [hrs, integral_entry_mul_eq_zero_of_row_ne r s c d hrs]

end FreeProbability.Orthogonal

import FreeProbability.RandomMatrix.OrthogonalFourthMoment
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import FreeProbability.Matrix.HermitianResolvent

/-! # Quadratic forms of a genuine Haar orthogonal row -/

namespace FreeProbability.Orthogonal

open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

def rowQuadraticForm (B : Matrix n n ℝ) (r : n) (U : Group n) : ℝ :=
  (fun i => U r i) ⬝ᵥ B *ᵥ (fun i => U r i)

theorem continuous_rowQuadraticForm (B : Matrix n n ℝ) (r : n) :
    Continuous (rowQuadraticForm B r) := by
  unfold rowQuadraticForm Matrix.mulVec dotProduct
  apply continuous_finsetSum
  intro i _
  have hi : Continuous (fun U : Group n => U r i) :=
    (continuous_apply i).comp ((continuous_apply r).comp continuous_subtype_val)
  apply hi.mul
  apply continuous_finsetSum
  intro j _
  exact continuous_const.mul
    ((continuous_apply j).comp ((continuous_apply r).comp continuous_subtype_val))

theorem integrable_rowQuadraticForm (B : Matrix n n ℝ) (r : n) :
    Integrable (rowQuadraticForm B r) (haar n) :=
  (continuous_rowQuadraticForm B r).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem rowQuadraticForm_eq_sum (B : Matrix n n ℝ) (r : n) (U : Group n) :
    rowQuadraticForm B r U = ∑ i, ∑ j, B i j * (U r i * U r j) := by
  unfold rowQuadraticForm Matrix.mulVec dotProduct
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem integrable_weighted_row_pair (B : Matrix n n ℝ) (r i j : n) :
    Integrable (fun U : Group n => B i j * (U r i * U r j)) (haar n) := by
  have hi : Continuous (fun U : Group n => U r i) :=
    (continuous_apply i).comp ((continuous_apply r).comp continuous_subtype_val)
  have hj : Continuous (fun U : Group n => U r j) :=
    (continuous_apply j).comp ((continuous_apply r).comp continuous_subtype_val)
  exact (continuous_const.mul (hi.mul hj)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem integral_rowQuadraticForm (B : Matrix n n ℝ) (r : n) :
    (∫ U : Group n, rowQuadraticForm B r U ∂haar n) = B.trace / (Fintype.card n : ℝ) := by
  simp_rw [rowQuadraticForm_eq_sum]
  rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum _
    (fun j _ => integrable_weighted_row_pair B r i j))]
  have hrow (i : n) :
      (∫ U : Group n, ∑ j, B i j * (U r i * U r j) ∂haar n) =
        B i i / (Fintype.card n : ℝ) := by
    rw [integral_finsetSum _ (fun j _ => integrable_weighted_row_pair B r i j)]
    simp_rw [integral_const_mul, integral_entry_mul]
    simp [mul_ite, div_eq_mul_inv]
  simp_rw [hrow]
  rw [← Finset.sum_div]
  rfl

theorem rowQuadraticForm_sq_eq_sum (B : Matrix n n ℝ) (r : n) (U : Group n) :
    rowQuadraticForm B r U ^ 2 = ∑ i, ∑ j, ∑ k, ∑ l,
      (B i j * B k l) * (U r i * U r j * U r k * U r l) := by
  rw [rowQuadraticForm_eq_sum, pow_two, Finset.sum_mul_sum]
  simp_rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem integral_rowQuadraticForm_sq_eq_fourSum (B : Matrix n n ℝ) (r : n) :
    (∫ U : Group n, rowQuadraticForm B r U ^ 2 ∂haar n) =
      ∑ i, ∑ j, ∑ k, ∑ l, (B i j * B k l) *
        (∫ U : Group n, U r i * U r j * U r k * U r l ∂haar n) := by
  let f := fun i j k l (U : Group n) => (B i j * B k l) * (U r i * U r j * U r k * U r l)
  have h4 (i j k l : n) : Integrable (f i j k l) (haar n) :=
    (integrable_row_product_four r i j k l).const_mul _
  have h3 (i j k : n) : Integrable (fun U => ∑ l, f i j k l U) (haar n) :=
    integrable_finsetSum _ (fun l _ => h4 i j k l)
  have h2 (i j : n) : Integrable (fun U => ∑ k, ∑ l, f i j k l U) (haar n) :=
    integrable_finsetSum _ (fun k _ => h3 i j k)
  have h1 (i : n) : Integrable (fun U => ∑ j, ∑ k, ∑ l, f i j k l U) (haar n) :=
    integrable_finsetSum _ (fun j _ => h2 i j)
  simp_rw [rowQuadraticForm_sq_eq_sum]
  change (∫ U : Group n, ∑ i, ∑ j, ∑ k, ∑ l, f i j k l U ∂haar n) = _
  rw [integral_finsetSum _ (fun i _ => h1 i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => h2 i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum _ (fun k _ => h3 i j k)]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_finsetSum _ (fun l _ => h4 i j k l)]
  apply Finset.sum_congr rfl
  intro l _
  exact integral_const_mul _ _

theorem integral_rowQuadraticForm_sq (B : Matrix n n ℝ) (r : n) :
    (∫ U : Group n, rowQuadraticForm B r U ^ 2 ∂haar n) =
      (B.trace ^ 2 + (Bᵀ * B).trace + (B * B).trace) /
        ((Fintype.card n : ℝ) * ((Fintype.card n : ℝ) + 2)) := by
  rw [integral_rowQuadraticForm_sq_eq_fourSum]
  simp_rw [integral_row_product_four, ← mul_div_assoc, ← Finset.sum_div,
    mul_add, Finset.sum_add_distrib]
  congr 1
  have h1 : (∑ i : n, ∑ j : n, ∑ k : n, ∑ l : n,
      (B i j * B k l) * (if i = j ∧ k = l then (1 : ℝ) else 0)) = B.trace ^ 2 := by
    simp [ite_and, mul_ite, Matrix.trace, pow_two, Finset.sum_mul_sum]
  have h2 : (∑ i : n, ∑ j : n, ∑ k : n, ∑ l : n,
      (B i j * B k l) * (if i = k ∧ j = l then (1 : ℝ) else 0)) = (Bᵀ * B).trace := by
    simp [ite_and, mul_ite, Matrix.trace, Matrix.mul_apply]
    rw [Finset.sum_comm]
  have h3 : (∑ i : n, ∑ j : n, ∑ k : n, ∑ l : n,
      (B i j * B k l) * (if i = l ∧ j = k then (1 : ℝ) else 0)) = (B * B).trace := by
    simp [ite_and, mul_ite, Matrix.trace, Matrix.mul_apply]
  rw [h1, h2, h3]

theorem integral_rowQuadraticForm_sq_of_symmetric (B : Matrix n n ℝ) (r : n) (hB : Bᵀ = B) :
    (∫ U : Group n, rowQuadraticForm B r U ^ 2 ∂haar n) =
      (B.trace ^ 2 + 2 * (B * B).trace) /
        ((Fintype.card n : ℝ) * ((Fintype.card n : ℝ) + 2)) := by
  rw [integral_rowQuadraticForm_sq, hB]
  congr 1
  ring

theorem memLp_rowQuadraticForm (B : Matrix n n ℝ) (r : n) :
    MemLp (rowQuadraticForm B r) 2 (haar n) :=
  (continuous_rowQuadraticForm B r).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Exact variance, without replacing the finite-dimensional law by a limiting one. -/
theorem variance_rowQuadraticForm_of_symmetric (B : Matrix n n ℝ) (r : n) (hB : Bᵀ = B) :
    ProbabilityTheory.variance (rowQuadraticForm B r) (haar n) =
      2 / ((Fintype.card n : ℝ) * ((Fintype.card n : ℝ) + 2)) *
        ((B * B).trace - B.trace ^ 2 / (Fintype.card n : ℝ)) := by
  rw [ProbabilityTheory.variance_eq_sub (memLp_rowQuadraticForm B r)]
  change (∫ U : Group n, rowQuadraticForm B r U ^ 2 ∂haar n) -
    (∫ U : Group n, rowQuadraticForm B r U ∂haar n) ^ 2 = _
  rw [integral_rowQuadraticForm_sq_of_symmetric B r hB, integral_rowQuadraticForm]
  have hN : (Fintype.card n : ℝ) ≠ 0 := by
    let _ : Nonempty n := ⟨r⟩
    exact_mod_cast Fintype.card_ne_zero
  have hNr : (0 : ℝ) < Fintype.card n := lt_of_le_of_ne (by positivity) hN.symm
  have hN2 : (Fintype.card n : ℝ) + 2 ≠ 0 := by linarith
  field_simp [hN, hN2]
  ring

theorem variance_rowQuadraticForm_le (B : Matrix n n ℝ) (r : n) (hB : Bᵀ = B) :
    ProbabilityTheory.variance (rowQuadraticForm B r) (haar n) ≤
      2 * ‖B‖ ^ 2 / ((Fintype.card n : ℝ) + 2) := by
  have hNr : (0 : ℝ) < Fintype.card n := by
    let _ : Nonempty n := ⟨r⟩
    exact_mod_cast Fintype.card_pos
  have hN : (Fintype.card n : ℝ) ≠ 0 := hNr.ne'
  have hN2 : (Fintype.card n : ℝ) + 2 ≠ 0 := by linarith
  have hcoef : 0 ≤ 2 / ((Fintype.card n : ℝ) * ((Fintype.card n : ℝ) + 2)) := by positivity
  have hh : B.IsHermitian := by
    change Bᴴ = B
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hB
  have htrace := hermitian_trace_sq_le_card_mul_norm_sq hh
  rw [variance_rowQuadraticForm_of_symmetric B r hB]
  calc
    _ ≤ 2 / ((Fintype.card n : ℝ) * ((Fintype.card n : ℝ) + 2)) * (B * B).trace :=
      mul_le_mul_of_nonneg_left (sub_le_self _ (div_nonneg (sq_nonneg _) hNr.le)) hcoef
    _ ≤ 2 / ((Fintype.card n : ℝ) * ((Fintype.card n : ℝ) + 2)) *
        ((Fintype.card n : ℝ) * ‖B‖ ^ 2) := mul_le_mul_of_nonneg_left htrace hcoef
    _ = _ := by field_simp [hN, hN2]

/-- An unconditional deviation bound for a quadratic form of a genuine Haar row. -/
theorem measure_rowQuadraticForm_deviation_le (B : Matrix n n ℝ) (r : n) (hB : Bᵀ = B)
    (ε : ℝ) (hε : 0 < ε) :
    haar n {U | ε ≤ |rowQuadraticForm B r U - B.trace / (Fintype.card n : ℝ)|} ≤
      ENNReal.ofReal (2 * ‖B‖ ^ 2 / (((Fintype.card n : ℝ) + 2) * ε ^ 2)) := by
  have h := ProbabilityTheory.meas_ge_le_variance_div_sq (memLp_rowQuadraticForm B r) hε
  rw [integral_rowQuadraticForm] at h
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (2 * ‖B‖ ^ 2 / ((Fintype.card n : ℝ) + 2)) / ε ^ 2 :=
      div_le_div_of_nonneg_right (variance_rowQuadraticForm_le B r hB) (sq_nonneg _)
    _ = _ := div_div _ _ _

end FreeProbability.Orthogonal

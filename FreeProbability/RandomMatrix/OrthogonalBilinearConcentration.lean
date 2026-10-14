import FreeProbability.RandomMatrix.OrthogonalLinearMoment
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Summable fourth-moment bounds for independent Haar-row bilinear forms

Independence is represented by the genuine product Haar probability. Conditional
kernel-sphere disintegration is a separate obligation.
-/

namespace FreeProbability.Orthogonal

open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

def bilinearRowForm (B : Matrix n m ℝ) (r : n) (s : m) (p : Group n × Group m) : ℝ :=
  (fun i => p.1 r i) ⬝ᵥ B *ᵥ (fun j => p.2 s j)

theorem continuous_bilinearRowForm (B : Matrix n m ℝ) (r : n) (s : m) :
    Continuous (bilinearRowForm B r s) := by
  unfold bilinearRowForm Matrix.mulVec dotProduct
  apply continuous_finsetSum
  intro i _
  have hentry : Continuous (fun U : Group n => U r i) :=
    (continuous_apply i).comp ((continuous_apply r).comp continuous_subtype_val)
  have hi : Continuous (fun p : Group n × Group m => p.1 r i) :=
    hentry.comp continuous_fst
  apply hi.mul
  apply continuous_finsetSum
  intro j _
  have hentry' : Continuous (fun V : Group m => V s j) :=
    (continuous_apply j).comp ((continuous_apply s).comp continuous_subtype_val)
  exact continuous_const.mul (hentry'.comp continuous_snd)

theorem integrable_bilinearRowForm_pow (B : Matrix n m ℝ) (r : n) (s : m) (k : ℕ) :
    Integrable (fun p => bilinearRowForm B r s p ^ k) ((haar n).prod (haar m)) :=
  ((continuous_bilinearRowForm B r s).pow k).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem haar_row_norm (V : Group m) (s : m) : ‖WithLp.toLp 2 (fun j => V s j)‖ = 1 := by
  have hs : ‖WithLp.toLp 2 (fun j => V s j)‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact sum_row_sq V s
  nlinarith [norm_nonneg (WithLp.toLp 2 (fun j => V s j))]

theorem integral_bilinearRowForm_pow_four_le (B : Matrix n m ℝ) (r : n) (s : m) :
    (∫ p, bilinearRowForm B r s p ^ 4 ∂(haar n).prod (haar m)) ≤
      3 * ‖B‖ ^ 4 / ((Fintype.card n : ℝ) * ((Fintype.card n : ℝ) + 2)) := by
  have hf := integrable_bilinearRowForm_pow B r s 4
  rw [integral_prod_symm _ hf]
  have hpoint (V : Group m) :
      (∫ U : Group n, bilinearRowForm B r s (U, V) ^ 4 ∂haar n) ≤
        3 * ‖B‖ ^ 4 / ((Fintype.card n : ℝ) * ((Fintype.card n : ℝ) + 2)) := by
    change (∫ U : Group n, rowLinearForm (B *ᵥ (fun j => V s j)) r U ^ 4 ∂haar n) ≤ _
    rw [integral_rowLinearForm_pow_four_norm]
    have hop := Matrix.l2_opNorm_mulVec B (WithLp.toLp 2 (fun j => V s j))
    change ‖WithLp.toLp 2 (B *ᵥ (fun j => V s j))‖ ≤
      ‖B‖ * ‖WithLp.toLp 2 (fun j => V s j)‖ at hop
    rw [haar_row_norm, mul_one] at hop
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact pow_le_pow_left₀ (norm_nonneg _) hop 4
  have h := integral_mono hf.integral_prod_right (integrable_const _) hpoint
  simpa using h

/-- A summable-in-dimension deviation bound for independent Haar rows. -/
theorem measure_bilinearRowForm_deviation_le (B : Matrix n m ℝ) (r : n) (s : m)
    (ε : ℝ) (hε : 0 < ε) :
    (haar n).prod (haar m) {p | ε ≤ |bilinearRowForm B r s p|} ≤
      ENNReal.ofReal (3 * ‖B‖ ^ 4 /
        (((Fintype.card n : ℝ) * ((Fintype.card n : ℝ) + 2)) * ε ^ 4)) := by
  let μ := (haar n).prod (haar m)
  have hp : 0 < ε ^ 4 := pow_pos hε _
  have he : {p : Group n × Group m | ε ^ 4 ≤ bilinearRowForm B r s p ^ 4} =
      {p | ε ≤ |bilinearRowForm B r s p|} := by
    ext p
    change (ε ^ 4 ≤ bilinearRowForm B r s p ^ 4) ↔ ε ≤ |bilinearRowForm B r s p|
    rw [← (show Even 4 by decide).pow_abs (bilinearRowForm B r s p)]
    exact pow_le_pow_iff_left₀ (n := 4) hε.le (abs_nonneg _) (by decide)
  have hnonneg : 0 ≤ᵐ[μ] (fun p => bilinearRowForm B r s p ^ 4) :=
    Filter.Eventually.of_forall (fun p => by positivity)
  have hmark := mul_meas_ge_le_integral_of_nonneg hnonneg
    (integrable_bilinearRowForm_pow B r s 4) (ε ^ 4)
  rw [he] at hmark
  have hbound := hmark.trans (integral_bilinearRowForm_pow_four_le B r s)
  have hr : μ.real {p | ε ≤ |bilinearRowForm B r s p|} ≤
      3 * ‖B‖ ^ 4 / (((Fintype.card n : ℝ) * ((Fintype.card n : ℝ) + 2)) * ε ^ 4) := by
    rw [← div_div]
    apply (le_div_iff₀ hp).mpr
    simpa [mul_comm] using hbound
  have hof := ENNReal.ofReal_le_ofReal hr
  rw [ofReal_measureReal] at hof
  exact hof

end FreeProbability.Orthogonal

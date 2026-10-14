import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Basic.Real.Basic

/-!
# Rank-one secular equation

For an exterior parameter where `z I - A` is invertible, the rank-one update
has an eigenvalue at `z` exactly when its scalar secular denominator vanishes.
The deterministic no-outlier test needs an explicit resolvent quadratic-form
bound. Establishing that bound for random matrices remains an analytic obligation.
-/

namespace FreeProbability

open Matrix

variable {𝕜 n : Type*} [Field 𝕜] [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
theorem replicate_product_eq_outer (u v : n → 𝕜) :
    replicateCol Unit u * replicateRow Unit v = vecMulVec u v := by
  ext i j
  simp [mul_apply, vecMulVec_apply]

/-- Matrix determinant lemma in scalar resolvent form. -/
theorem det_rankOne_add (A : Matrix n n 𝕜) (hA : A.det ≠ 0) (u v : n → 𝕜) :
    (A + vecMulVec u v).det = A.det * (1 + v ⬝ᵥ A⁻¹ *ᵥ u) := by
  have h := det_add_replicateCol_mul_replicateRow (ι := Unit)
    (isUnit_iff_ne_zero.mpr hA) u v
  rw [replicate_product_eq_outer, Matrix.mul_assoc, ← replicateCol_mulVec] at h
  simpa [Matrix.det_unique] using h

/-- The resolvent denominator for the update `A + u vᵀ`. -/
noncomputable def secular (A : Matrix n n 𝕜) (u v : n → 𝕜) (z : 𝕜) : 𝕜 :=
  1 - v ⬝ᵥ (z • (1 : Matrix n n 𝕜) - A)⁻¹ *ᵥ u

theorem det_rankOne_secular (A : Matrix n n 𝕜) (u v : n → 𝕜) (z : 𝕜)
    (hbase : (z • (1 : Matrix n n 𝕜) - A).det ≠ 0) :
    (z • (1 : Matrix n n 𝕜) - (A + vecMulVec u v)).det =
      (z • (1 : Matrix n n 𝕜) - A).det * secular A u v z := by
  have hn : vecMulVec (-u) v = -vecMulVec u v := by ext i j; simp
  have he : z • (1 : Matrix n n 𝕜) - (A + vecMulVec u v) =
      (z • (1 : Matrix n n 𝕜) - A) + vecMulVec (-u) v := by
    rw [hn]
    abel
  rw [he, det_rankOne_add _ hbase]
  simp only [secular, Matrix.mulVec_neg, dotProduct_neg, sub_eq_add_neg]

/-- Rank-one secular criterion for invertibility, with base resolvent existence explicit. -/
theorem rankOne_isUnit_iff (A : Matrix n n 𝕜) (u v : n → 𝕜) (z : 𝕜)
    (hbase : (z • (1 : Matrix n n 𝕜) - A).det ≠ 0) :
    IsUnit (z • (1 : Matrix n n 𝕜) - (A + vecMulVec u v)) ↔ secular A u v z ≠ 0 := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, det_rankOne_secular A u v z hbase]
  simp [hbase]

/-- Singular rank-one updates are precisely the zeros of the secular denominator. -/
theorem rankOne_det_eq_zero_iff (A : Matrix n n 𝕜) (u v : n → 𝕜) (z : 𝕜)
    (hbase : (z • (1 : Matrix n n 𝕜) - A).det ≠ 0) :
    (z • (1 : Matrix n n 𝕜) - (A + vecMulVec u v)).det = 0 ↔ secular A u v z = 0 := by
  rw [det_rankOne_secular A u v z hbase]
  simp [hbase]

/-- Eigenvalue in the elementary nonzero-eigenvector sense. -/
def IsMatrixEigenvalue (A : Matrix n n 𝕜) (z : 𝕜) : Prop :=
  ∃ x : n → 𝕜, x ≠ 0 ∧ A *ᵥ x = z • x

theorem matrixEigenvalue_iff_det_eq_zero (A : Matrix n n 𝕜) (z : 𝕜) :
    IsMatrixEigenvalue A z ↔ (z • (1 : Matrix n n 𝕜) - A).det = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨x, hx, he⟩
    exact ⟨x, hx, by simp [Matrix.sub_mulVec, Matrix.smul_mulVec, he]⟩
  · rintro ⟨x, hx, he⟩
    have he' : z • x - A *ᵥ x = 0 := by
      simpa [Matrix.sub_mulVec, Matrix.smul_mulVec] using he
    exact ⟨x, hx, (sub_eq_zero.mp he').symm⟩

/-- The scalar secular equation exactly characterizes every eigenvalue outside
the base spectrum. -/
theorem rankOne_isEigenvalue_iff (A : Matrix n n 𝕜) (u v : n → 𝕜) (z : 𝕜)
    (hbase : (z • (1 : Matrix n n 𝕜) - A).det ≠ 0) :
    IsMatrixEigenvalue (A + vecMulVec u v) z ↔ secular A u v z = 0 := by
  rw [matrixEigenvalue_iff_det_eq_zero, rankOne_det_eq_zero_iff A u v z hbase]

/-- A real resolvent form strictly below one excludes a singularity of the update. -/
theorem rankOne_noOutlier_of_lt (A : Matrix n n ℝ) (u v : n → ℝ) (z : ℝ)
    (hbase : (z • (1 : Matrix n n ℝ) - A).det ≠ 0)
    (hbound : v ⬝ᵥ (z • (1 : Matrix n n ℝ) - A)⁻¹ *ᵥ u < 1) :
    IsUnit (z • (1 : Matrix n n ℝ) - (A + vecMulVec u v)) := by
  apply (rankOne_isUnit_iff A u v z hbase).mpr
  exact sub_ne_zero.mpr (ne_of_gt hbound)

/-- A uniform exterior resolvent-form bound excludes every exterior eigenvalue.
The two input bounds are explicit; no probabilistic estimate is assumed silently. -/
theorem rankOne_noOutliers_above (A : Matrix n n ℝ) (u v : n → ℝ) (edge : ℝ)
    (hbase : ∀ z, edge < z → (z • (1 : Matrix n n ℝ) - A).det ≠ 0)
    (hbound : ∀ z, edge < z → v ⬝ᵥ (z • (1 : Matrix n n ℝ) - A)⁻¹ *ᵥ u < 1) :
    ∀ z, edge < z → ¬IsMatrixEigenvalue (A + vecMulVec u v) z := by
  intro z hz
  rw [rankOne_isEigenvalue_iff A u v z (hbase z hz)]
  exact sub_ne_zero.mpr (ne_of_gt (hbound z hz))

/-- The Sherman–Morrison inverse formula, with the scalar denominator condition
explicit and no ambient commutativity assumption on matrices. -/
theorem rankOne_inverse (A : Matrix n n 𝕜) (hA : A.det ≠ 0) (u v : n → 𝕜)
    (hden : 1 + v ⬝ᵥ A⁻¹ *ᵥ u ≠ 0) :
    (A + vecMulVec u v)⁻¹ = A⁻¹ -
      (1 + v ⬝ᵥ A⁻¹ *ᵥ u)⁻¹ • vecMulVec (A⁻¹ *ᵥ u) (v ᵥ* A⁻¹) := by
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  apply Matrix.inv_eq_right_inv
  rw [add_mul, mul_sub, mul_sub, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.mul_nonsing_inv A hunit, Matrix.vecMulVec_mul, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul_vecMulVec, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv A hunit, Matrix.one_mulVec, Matrix.vecMulVec_smul, smul_smul]
  have hcoef : (1 + v ⬝ᵥ A⁻¹ *ᵥ u)⁻¹ +
      (1 + v ⬝ᵥ A⁻¹ *ᵥ u)⁻¹ * (v ⬝ᵥ A⁻¹ *ᵥ u) = 1 := by
    calc
      _ = (1 + v ⬝ᵥ A⁻¹ *ᵥ u)⁻¹ * (1 + v ⬝ᵥ A⁻¹ *ᵥ u) := by ring
      _ = 1 := inv_mul_cancel₀ hden
  calc
    _ = 1 + (vecMulVec u (v ᵥ* A⁻¹) -
      ((1 + v ⬝ᵥ A⁻¹ *ᵥ u)⁻¹ • vecMulVec u (v ᵥ* A⁻¹) +
       ((1 + v ⬝ᵥ A⁻¹ *ᵥ u)⁻¹ * (v ⬝ᵥ A⁻¹ *ᵥ u)) • vecMulVec u (v ᵥ* A⁻¹))) := by abel
    _ = 1 := by rw [← add_smul, hcoef, one_smul, sub_self, add_zero]

/-- Rank-one resolvent update in the sign convention used by Cauchy transforms. -/
theorem rankOne_resolvent (A : Matrix n n 𝕜) (u v : n → 𝕜) (z : 𝕜)
    (hbase : (z • (1 : Matrix n n 𝕜) - A).det ≠ 0) (hden : secular A u v z ≠ 0) :
    (z • (1 : Matrix n n 𝕜) - (A + vecMulVec u v))⁻¹ =
      (z • (1 : Matrix n n 𝕜) - A)⁻¹ + (secular A u v z)⁻¹ •
        vecMulVec ((z • (1 : Matrix n n 𝕜) - A)⁻¹ *ᵥ u)
          (v ᵥ* (z • (1 : Matrix n n 𝕜) - A)⁻¹) := by
  have hn : vecMulVec (-u) v = -vecMulVec u v := by ext i j; simp
  have he : z • (1 : Matrix n n 𝕜) - (A + vecMulVec u v) =
      (z • (1 : Matrix n n 𝕜) - A) + vecMulVec (-u) v := by rw [hn]; abel
  have hd : 1 + v ⬝ᵥ (z • (1 : Matrix n n 𝕜) - A)⁻¹ *ᵥ (-u) ≠ 0 := by
    simpa only [secular, Matrix.mulVec_neg, dotProduct_neg, sub_eq_add_neg] using hden
  rw [he, rankOne_inverse _ hbase (-u) v hd]
  simp only [Matrix.mulVec_neg, Matrix.neg_vecMulVec, smul_neg, sub_neg_eq_add]
  simp only [secular, dotProduct_neg, sub_eq_add_neg]

end FreeProbability

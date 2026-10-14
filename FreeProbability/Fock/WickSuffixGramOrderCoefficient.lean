import FreeProbability.Fock.WickSuffixGramOrderCauchySchwarz
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import FreeProbability.Fock.WickNormWord

/-! # Actual scalar-matrix embeddings and diagonal word operator representations -/
noncomputable section
open scoped Classical ComplexOrder
namespace FreeProbability.Fock
variable {I ν : Type*} [Fintype ν]

/-- Scalar matrix coefficients embedded as genuine identity word operators. -/
def matrixScalarEmbed (C : Matrix ν ν ℂ) : CStarMatrix ν ν (WordSpace I →L[ℂ] WordSpace I) :=
  matrixWickTerm C []

/-- Actual diagonal star representation of every bounded word operator. -/
def wordDiagonalHom : (WordSpace I →L[ℂ] WordSpace I) →⋆ₐ[ℂ]
    CStarMatrix ν ν (WordSpace I →L[ℂ] WordSpace I) where
  toAlgHom := (CStarMatrix.ofMatrixStarAlgEquiv.toStarAlgHom.toAlgHom).comp
    (Matrix.scalarAlgHom ν ℂ)
  map_star' T := by
    apply CStarMatrix.ext
    intro i j
    change (Matrix.scalar ν (star T)) i j = star ((Matrix.scalar ν T) j i)
    by_cases h : i = j
    · simp [Matrix.scalar, Matrix.diagonal, h]
    · simp [Matrix.scalar, Matrix.diagonal, h, Ne.symm h]

/-- Exact factorization preserves actual matrix coefficient and operator order. -/
theorem matrixWickTerm_factor (C : Matrix ν ν ℂ) (w : List I) :
    matrixWickTerm C w = matrixScalarEmbed C * wordDiagonalHom (ν := ν) (wick w) := by
  apply CStarMatrix.ext
  intro i j
  change C i j • wick w = ∑ k, (C i k • (1 : WordSpace I →L[ℂ] WordSpace I)) *
    (Matrix.scalar ν (wick w)) k j
  simp [Matrix.scalar, Matrix.diagonal, smul_mul_assoc]

/-- The actual scalar-matrix embedding retains the exact coefficient star-square. -/
theorem matrixScalarEmbed_mul_star (C : Matrix ν ν ℂ) :
    matrixScalarEmbed (I := I) C * star (matrixScalarEmbed C) =
      matrixScalarEmbed (C * C.conjTranspose) := by
  rw [matrixScalarEmbed, matrixScalarEmbed, matrixWickTerm_mul_star]
  apply CStarMatrix.ext
  intro i j
  simp [matrixWickTerm]

/-- A genuine all-vector operator norm-square order bound. -/
theorem operator_mul_star_le_normBound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (T : E →L[ℂ] E) (c : ℝ) (hc : ‖T‖ ≤ c) :
    T * star T ≤ ((c ^ 2 : ℝ) : ℂ) • (1 : E →L[ℂ] E) := by
  rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_iff_complex]
  intro f
  have ht : ‖star T f‖ ≤ c * ‖f‖ := by
    have hh := (star T).le_opNorm f
    rw [norm_star] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hc (norm_nonneg f))
  have hc0 : 0 ≤ c := (norm_nonneg T).trans hc
  have hsq : ‖star T f‖ ^ 2 ≤ c ^ 2 * ‖f‖ ^ 2 := by
    calc
      _ ≤ (c * ‖f‖) ^ 2 := by gcongr
      _ = _ := mul_pow _ _ _
  have hi : inner ℂ ((T * star T) f) f = (‖star T f‖ ^ 2 : ℝ) := by
    rw [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
      ← ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    norm_cast
  have he : inner ℂ ((((c ^ 2 : ℝ) : ℂ) • (1 : E →L[ℂ] E) - T * star T) f) f =
      (c ^ 2 * ‖f‖ ^ 2 - ‖star T f‖ ^ 2 : ℝ) := by
    rw [sub_apply, smul_apply, one_apply_eq_self, inner_sub_left, inner_smul_left,
      inner_self_eq_norm_sq_to_K, hi]
    simp only [Complex.conj_ofReal]
    push_cast
    rfl
  rw [he]
  let q : ℝ := c ^ 2 * ‖f‖ ^ 2 - ‖star T f‖ ^ 2
  constructor
  · change (Complex.re (Complex.ofReal q) : ℂ) = Complex.ofReal q
    rw [Complex.ofReal_re]
  · change 0 ≤ Complex.re (Complex.ofReal q)
    rw [Complex.ofReal_re]
    exact sub_nonneg.mpr hsq

/-- The actual single-word norm estimate gives a full operator-order square bound. -/
theorem wick_mul_star_le_length_square (w : List I) :
    wick w * star (wick w) ≤ ((((w.length : ℝ) + 1) ^ 2 : ℝ) : ℂ) •
      (1 : WordSpace I →L[ℂ] WordSpace I) :=
  operator_mul_star_le_normBound (wick w) _ (norm_wick_le_length_add_one w)

attribute [local irreducible] wordDiagonalHom matrixScalarEmbed matrixWickTerm

/-- A coefficient term square is bounded by its actual scalar matrix marginal. -/
theorem matrixWickTerm_mul_star_le (C : Matrix ν ν ℂ) (w : List I) :
    matrixWickTerm C w * star (matrixWickTerm C w) ≤
      ((((w.length : ℝ) + 1) ^ 2 : ℝ) : ℂ) • matrixScalarEmbed (I := I) (C * C.conjTranspose) := by
  have hW := wick_mul_star_le_length_square w
  have hD := map_nonneg (wordDiagonalHom (I := I) (ν := ν)) (sub_nonneg.mpr hW)
  rw [map_sub, map_mul, map_star, map_smul, map_one] at hD
  have hc := star_right_conjugate_le_conjugate (sub_nonneg.mp hD) (matrixScalarEmbed (I := I) C)
  let A : CStarMatrix ν ν (WordSpace I →L[ℂ] WordSpace I) := matrixScalarEmbed C
  let B : CStarMatrix ν ν (WordSpace I →L[ℂ] WordSpace I) := wordDiagonalHom (wick w)
  have hf : matrixWickTerm C w = A * B := matrixWickTerm_factor C w
  have hs : star (A * B) = star B * star A := star_mul A B
  calc
    _ = A * (B * star B) * star A := by
      rw [hf, hs]
      simp only [mul_assoc]
    _ ≤ _ := by
      change A * (B * star B) * star A ≤ _ at hc
      have hr : matrixScalarEmbed (I := I) (C * C.conjTranspose) = A * star A :=
        (matrixScalarEmbed_mul_star C).symm
      rw [hr]
      simpa only [mul_smul_comm, smul_mul_assoc, mul_one] using hc

end FreeProbability.Fock

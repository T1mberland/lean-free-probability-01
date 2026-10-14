import FreeProbability.OperatorValued.MatrixExpectation
import FreeProbability.Algebraic.StarProbabilitySpace
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.BigOperators
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! # Genuine matrix Gram positivity of positive scalar states -/

namespace FreeProbability

open Matrix
open scoped ComplexOrder

variable {A n m : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
  [Fintype n] [DecidableEq n] [Fintype m]

omit [StarRing A] [StarModule ℂ A] in
private theorem expectation_scalar_sandwich (φ : ProbabilitySpace ℂ A)
    (c d : ℂ) (x : A) :
    φ.expectation (algebraMap ℂ A c * x * algebraMap ℂ A d) = c * φ.expectation x * d := by
  rw [← Algebra.commutes d (algebraMap ℂ A c * x), ← Algebra.smul_def, map_smul, smul_eq_mul]
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  ac_rfl

omit [DecidableEq n] in
/-- The scalar quadratic form of the entrywise expectation is the expectation
of the same quadratic form with algebraically embedded scalar coefficients. -/
theorem matrixExpectation_quadratic (φ : StarProbabilitySpace A) (M : Matrix n n A)
    (v : n → ℂ) :
    star v ⬝ᵥ (matrixExpectation φ.toProbabilitySpace M *ᵥ v) =
      φ.expectation (star (algebraMap ℂ A ∘ v) ⬝ᵥ (M *ᵥ (algebraMap ℂ A ∘ v))) := by
  classical
  simp only [dotProduct, mulVec, Finset.mul_sum, map_sum, Pi.star_apply,
    matrixExpectation_apply, Function.comp_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← algebraMap_star_comm]
  simpa only [mul_assoc] using
    (expectation_scalar_sandwich φ.toProbabilitySpace (star (v i)) (v j) (M i j)).symm

omit [DecidableEq n] in
/-- Positivity on scalar-state squares gives a full positive semidefinite Gram
matrix at every finite matrix size, even for rectangular algebra-valued arrays. -/
theorem matrixExpectation_gram_posSemidef (φ : StarProbabilitySpace A) (X : Matrix m n A) :
    (matrixExpectation φ.toProbabilitySpace (Xᴴ * X)).PosSemidef := by
  classical
  apply PosSemidef.of_dotProduct_mulVec_nonneg
  · change ((Xᴴ * X).map φ.expectation).IsHermitian
    exact (isHermitian_conjTranspose_mul_self X).map φ.expectation (fun x => φ.map_star x)
  · intro v
    rw [matrixExpectation_quadratic, ← mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose, star_star]
    rw [dotProduct, map_sum]
    exact Finset.sum_nonneg (fun i _ => φ.positive _)

end FreeProbability

import FreeProbability.OperatorValued.ConditionalExpectation
import Mathlib.Data.Matrix.Basic

/-!
# Actual matrix conditional expectations from scalar expectations

A normalized scalar expectation acts entrywise on matrices. The coefficient
algebra is the actual range of the scalar-matrix embedding, and the resulting
conditional expectation fixes that range and satisfies both bimodule identities.
This module is algebraic; complete positivity is a separate matrix-state result.
-/

namespace FreeProbability

variable {𝕜 A n : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A] [Fintype n] [DecidableEq n]

/-- Apply the scalar expectation to every matrix entry. -/
def matrixExpectation (φ : ProbabilitySpace 𝕜 A) : Matrix n n A →ₗ[𝕜] Matrix n n 𝕜 :=
  φ.expectation.mapMatrix

omit [Fintype n] [DecidableEq n] in
@[simp] theorem matrixExpectation_apply (φ : ProbabilitySpace 𝕜 A) (X : Matrix n n A) (i j : n) :
    matrixExpectation φ X i j = φ.expectation (X i j) := rfl

/-- Embed scalar matrices as genuine matrices over the ambient algebra. -/
def scalarMatrixEmbedding : Matrix n n 𝕜 →ₐ[𝕜] Matrix n n A :=
  (Algebra.ofId 𝕜 A).mapMatrix

@[simp] theorem scalarMatrixEmbedding_apply (C : Matrix n n 𝕜) (i j : n) :
    scalarMatrixEmbedding C i j = algebraMap 𝕜 A (C i j) := rfl

/-- The actual coefficient subalgebra in the amplified ambient algebra. -/
def scalarMatrixAlgebra (𝕜 A n : Type*) [Field 𝕜] [Ring A] [Algebra 𝕜 A]
    [Fintype n] [DecidableEq n] : Subalgebra 𝕜 (Matrix n n A) :=
  (scalarMatrixEmbedding : Matrix n n 𝕜 →ₐ[𝕜] Matrix n n A).range

@[simp] theorem matrixExpectation_scalarMatrixEmbedding (φ : ProbabilitySpace 𝕜 A)
    (C : Matrix n n 𝕜) : matrixExpectation φ (scalarMatrixEmbedding C) = C := by
  ext i j
  exact φ.expectation_algebraMap _

/-- Left scalar-matrix coefficients pass through the entrywise expectation. -/
theorem matrixExpectation_mul_left (φ : ProbabilitySpace 𝕜 A) (C : Matrix n n 𝕜)
    (X : Matrix n n A) :
    matrixExpectation φ (scalarMatrixEmbedding C * X) = C * matrixExpectation φ X := by
  ext i j
  change φ.expectation (∑ k, algebraMap 𝕜 A (C i k) * X k j) =
    ∑ k, C i k * φ.expectation (X k j)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

/-- Right scalar-matrix coefficients pass through, preserving matrix order. -/
theorem matrixExpectation_mul_right (φ : ProbabilitySpace 𝕜 A) (X : Matrix n n A)
    (C : Matrix n n 𝕜) :
    matrixExpectation φ (X * scalarMatrixEmbedding C) = matrixExpectation φ X * C := by
  ext i j
  change φ.expectation (∑ k, X i k * algebraMap 𝕜 A (C k j)) =
    ∑ k, φ.expectation (X i k) * C k j
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← (Algebra.commutes (C k j) (X i k)), ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

/-- The entrywise scalar expectation, with the embedded coefficient range as its
actual target, is an algebraic conditional expectation. -/
def matrixConditionalExpectation (φ : ProbabilitySpace 𝕜 A) :
    ConditionalExpectation (scalarMatrixAlgebra 𝕜 A n) where
  toLinearMap := scalarMatrixEmbedding.rangeRestrict.toLinearMap.comp (matrixExpectation φ)
  fixes := by
    intro C
    obtain ⟨D, hD⟩ := C.property
    apply Subtype.ext
    change scalarMatrixEmbedding (matrixExpectation φ C.val) = C.val
    rw [← hD]
    change scalarMatrixEmbedding (matrixExpectation φ (scalarMatrixEmbedding D)) = scalarMatrixEmbedding D
    rw [matrixExpectation_scalarMatrixEmbedding]
  map_mul_left := by
    intro C X
    obtain ⟨D, hD⟩ := C.property
    apply Subtype.ext
    change scalarMatrixEmbedding (matrixExpectation φ (C.val * X)) =
      C.val * scalarMatrixEmbedding (matrixExpectation φ X)
    rw [← hD]
    change scalarMatrixEmbedding (matrixExpectation φ (scalarMatrixEmbedding D * X)) =
      scalarMatrixEmbedding D * scalarMatrixEmbedding (matrixExpectation φ X)
    rw [matrixExpectation_mul_left, map_mul]
  map_mul_right := by
    intro X C
    obtain ⟨D, hD⟩ := C.property
    apply Subtype.ext
    change scalarMatrixEmbedding (matrixExpectation φ (X * C.val)) =
      scalarMatrixEmbedding (matrixExpectation φ X) * C.val
    rw [← hD]
    change scalarMatrixEmbedding (matrixExpectation φ (X * scalarMatrixEmbedding D)) =
      scalarMatrixEmbedding (matrixExpectation φ X) * scalarMatrixEmbedding D
    rw [matrixExpectation_mul_right, map_mul]

@[simp] theorem matrixConditionalExpectation_coe (φ : ProbabilitySpace 𝕜 A)
    (X : Matrix n n A) :
    ((matrixConditionalExpectation φ).toLinearMap X : Matrix n n A) =
      scalarMatrixEmbedding (matrixExpectation φ X) := rfl

end FreeProbability

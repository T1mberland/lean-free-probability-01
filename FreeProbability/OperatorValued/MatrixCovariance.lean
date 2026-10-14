import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Basic

/-!
# Hermitian matrix covariance and every finite amplification

For arbitrary finite Hermitian coefficients, the covariance is exactly
`D ↦ sum_i A_i D A_i`. Its amplification acts entrywise on matrix blocks and is
positive semidefinite at every finite matrix level, by actual conjugation proofs.
The coefficients need not be positive, commute, or sum to the identity.
-/

namespace FreeProbability

open Matrix
open scoped Kronecker ComplexOrder

variable {n I : Type*} [Fintype n] [DecidableEq n] [Fintype I]

/-- The Hermitian-coefficient covariance formula, as a complex linear map. -/
def matrixCovariance (A : I → Matrix n n ℂ) : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ where
  toFun D := ∑ i, A i * D * A i
  map_add' := by
    intro D E
    simp only [mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro c D
    simp only [mul_smul_comm, smul_mul_assoc, Finset.smul_sum, RingHom.id_apply]

@[simp] theorem matrixCovariance_apply (A : I → Matrix n n ℂ) (D : Matrix n n ℂ) :
    matrixCovariance A D = ∑ i, A i * D * A i := rfl

/-- Amplify a coefficient to identical copies on every matrix block. -/
def matrixAmplifiedCoefficient {k : Type*} [Fintype k] [DecidableEq k]
    (A : Matrix n n ℂ) : Matrix (k × n) (k × n) ℂ := (1 : Matrix k k ℂ) ⊗ₖ A

/-- The covariance at an arbitrary finite amplification level. -/
def matrixCovarianceAmplification {k : Type*} [Fintype k] [DecidableEq k]
    (A : I → Matrix n n ℂ) : Matrix (k × n) (k × n) ℂ →ₗ[ℂ] Matrix (k × n) (k × n) ℂ :=
  matrixCovariance (fun i => matrixAmplifiedCoefficient (A i))

/-- This is the actual entrywise matrix-block amplification of the base map. -/
theorem matrixCovarianceAmplification_block {k : Type*} [Fintype k] [DecidableEq k]
    (A : I → Matrix n n ℂ) (D : Matrix (k × n) (k × n) ℂ) (u v : k) (a b : n) :
    matrixCovarianceAmplification A D (u, a) (v, b) =
      matrixCovariance A (fun c d => D (u, c) (v, d)) a b := by
  classical
  change (∑ i, matrixAmplifiedCoefficient (k := k) (A i) * D * matrixAmplifiedCoefficient (k := k) (A i)) (u, a) (v, b) =
    (∑ i, A i * Matrix.of (fun c d => D (u, c) (v, d)) * A i) a b
  rw [Matrix.sum_apply, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp [matrixAmplifiedCoefficient, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply]

omit [Fintype n] [DecidableEq n] in
/-- Hermitian coefficients remain Hermitian at every finite amplification. -/
theorem matrixAmplifiedCoefficient_isHermitian {k : Type*} [Fintype k] [DecidableEq k]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (matrixAmplifiedCoefficient (k := k) A).IsHermitian := by
  unfold matrixAmplifiedCoefficient
  change ((1 : Matrix k k ℂ) ⊗ₖ A)ᴴ = (1 : Matrix k k ℂ) ⊗ₖ A
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, hA.eq]

/-- The exact covariance map preserves positive semidefinite matrices for
arbitrary finite Hermitian coefficients. -/
theorem matrixCovariance_posSemidef (A : I → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {D : Matrix n n ℂ} (hD : D.PosSemidef) :
    (matrixCovariance A D).PosSemidef := by
  classical
  apply Matrix.posSemidef_sum Finset.univ
  intro i _
  simpa only [(hA i).eq] using hD.conjTranspose_mul_mul_same (A i)

/-- Complete matrix positivity: every finite entrywise block amplification of
the exact Hermitian covariance preserves the full positive semidefinite cone. -/
theorem matrixCovarianceAmplification_posSemidef {k : Type*} [Fintype k] [DecidableEq k]
    (A : I → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {D : Matrix (k × n) (k × n) ℂ} (hD : D.PosSemidef) :
    (matrixCovarianceAmplification A D).PosSemidef :=
  matrixCovariance_posSemidef _ (fun i => matrixAmplifiedCoefficient_isHermitian (hA i)) hD

end FreeProbability

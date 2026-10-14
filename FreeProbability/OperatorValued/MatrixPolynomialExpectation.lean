import FreeProbability.OperatorValued.MatrixTensorPowers
import FreeProbability.OperatorValued.MatrixLinearCombination

/-! # Evaluating matrix linear polynomials and contracting tensor cuts -/

noncomputable section
open scoped Classical TensorProduct
namespace FreeProbability

variable {A n I : Type*} [Ring A] [Algebra ℂ A] [Fintype n] [DecidableEq n] [Fintype I]

/-- The actual polynomial matrix with the prescribed deterministic coefficients. -/
def matrixLinearPolynomial (C : I → Matrix n n ℂ) : Matrix n n (WordPolynomial ℂ I) :=
  matrixLinearCombination (fun i => wordMonomial [i]) C

/-- A constant coefficient matrix in the polynomial tensor bimodule. -/
def matrixConstantTensor (C : Matrix n n ℂ) : Matrix n n (PolynomialTensor ℂ I) :=
  fun r c => C r c • ((1 : WordPolynomial ℂ I) ⊗ₜ[ℂ] (1 : WordPolynomial ℂ I))

omit [Fintype n] [DecidableEq n] in
theorem matrixPolynomialEvaluate_linearPolynomial (a : I → A) (C : I → Matrix n n ℂ) :
    matrixPolynomialEvaluate a (matrixLinearPolynomial C) = matrixLinearCombination a C := by
  ext r c
  change evaluate a (∑ i, C i r c • wordMonomial [i]) = ∑ i, C i r c • a i
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  change C i r c • evaluate a (MonoidAlgebra.single (FreeMonoid.ofList [i]) 1) = _
  rw [evaluate_single]
  simp

omit [Fintype n] [DecidableEq n] in
theorem matrixFreeDifferenceQuotient_linearPolynomial (i : I) (C : I → Matrix n n ℂ) :
    matrixFreeDifferenceQuotient i (matrixLinearPolynomial C) = matrixConstantTensor (C i) := by
  ext r c
  change freeDifferenceQuotient i (∑ j, C j r c • wordMonomial [j]) = _
  simp only [map_sum, map_smul, freeDifferenceQuotient_generator, smul_ite, smul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rfl

omit [DecidableEq n] [Fintype I] in
theorem matrixPolynomialEvaluate_mul (a : I → A)
    (P Q : Matrix n n (WordPolynomial ℂ I)) :
    matrixPolynomialEvaluate a (P * Q) = matrixPolynomialEvaluate a P * matrixPolynomialEvaluate a Q := by
  ext r c
  simp [matrixPolynomialEvaluate, Matrix.mul_apply]

omit [Fintype n] [Fintype I] in
@[simp] theorem matrixPolynomialEvaluate_one (a : I → A) :
    matrixPolynomialEvaluate a (1 : Matrix n n (WordPolynomial ℂ I)) = 1 := by
  ext r c
  by_cases h : r = c <;> simp [matrixPolynomialEvaluate, Matrix.one_apply, h]

omit [Fintype I] in
theorem matrixPolynomialEvaluate_pow (a : I → A) (P : Matrix n n (WordPolynomial ℂ I)) (k : ℕ) :
    matrixPolynomialEvaluate a (P ^ k) = matrixPolynomialEvaluate a P ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, matrixPolynomialEvaluate_mul, ih, pow_succ]

omit [DecidableEq n] [Fintype I] in
/-- Contracting a tensor cut produces the two actual matrix expectations on
either side of its deterministic middle coefficient. -/
theorem matrixTensorPolynomialExpectation_cut (φ : ProbabilitySpace ℂ A) (a : I → A)
    (P Q : Matrix n n (WordPolynomial ℂ I)) (C : Matrix n n ℂ) :
    matrixTensorPolynomialExpectation φ a
      (matrixTensorLeft P (matrixTensorRight Q (matrixConstantTensor C))) =
      matrixExpectation φ (matrixPolynomialEvaluate a P) * C *
        matrixExpectation φ (matrixPolynomialEvaluate a Q) := by
  ext r c
  change tensorPolynomialExpectation φ a
      (∑ u, tensorLeft (P r u) (∑ v, tensorRight (Q v c)
        (C u v • ((1 : WordPolynomial ℂ I) ⊗ₜ[ℂ] (1 : WordPolynomial ℂ I))))) = _
  simp only [map_sum, map_smul, tensorRight_tmul, tensorLeft_tmul, mul_one, one_mul,
    tensorPolynomialExpectation_tmul, smul_eq_mul]
  simp only [Matrix.mul_apply, Finset.sum_mul, matrixExpectation,
    LinearMap.mapMatrix_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro u _
  ac_rfl

end FreeProbability

import FreeProbability.Fock.MatrixPolynomialIntegrationByParts

/-! # The genuine polynomial tensor bimodule at matrix level -/

noncomputable section
open scoped Classical TensorProduct

namespace FreeProbability

variable {𝕜 I n : Type*} [Field 𝕜] [Fintype n]

/-- Left multiplication of matrix polynomials on the first tensor factor. -/
def matrixTensorLeft (P : Matrix n n (WordPolynomial 𝕜 I)) :
    Matrix n n (PolynomialTensor 𝕜 I) →ₗ[𝕜] Matrix n n (PolynomialTensor 𝕜 I) where
  toFun Z r c := ∑ u, tensorLeft (P r u) (Z u c)
  map_add' := by
    intro Z W
    ext r c
    change (∑ u, tensorLeft (P r u) ((Z + W) u c)) =
      (∑ u, tensorLeft (P r u) (Z u c)) + ∑ u, tensorLeft (P r u) (W u c)
    simp only [Matrix.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' := by
    intro a Z
    ext r c
    change (∑ u, tensorLeft (P r u) ((a • Z) u c)) =
      a • ∑ u, tensorLeft (P r u) (Z u c)
    simp only [Matrix.smul_apply, map_smul, Finset.smul_sum]

/-- Right multiplication of matrix polynomials on the second tensor factor. -/
def matrixTensorRight (P : Matrix n n (WordPolynomial 𝕜 I)) :
    Matrix n n (PolynomialTensor 𝕜 I) →ₗ[𝕜] Matrix n n (PolynomialTensor 𝕜 I) where
  toFun Z r c := ∑ u, tensorRight (P u c) (Z r u)
  map_add' := by
    intro Z W
    ext r c
    change (∑ u, tensorRight (P u c) ((Z + W) r u)) =
      (∑ u, tensorRight (P u c) (Z r u)) + ∑ u, tensorRight (P u c) (W r u)
    simp only [Matrix.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' := by
    intro a Z
    ext r c
    change (∑ u, tensorRight (P u c) ((a • Z) r u)) =
      a • ∑ u, tensorRight (P u c) (Z r u)
    simp only [Matrix.smul_apply, map_smul, Finset.smul_sum]

private theorem tensorLeft_sum {α : Type*} (S : Finset α) (P : α → WordPolynomial 𝕜 I)
    (z : PolynomialTensor 𝕜 I) : tensorLeft (∑ i ∈ S, P i) z = ∑ i ∈ S, tensorLeft (P i) z := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih => simp [ha, tensorLeft_add, ih]

private theorem tensorRight_sum {α : Type*} (S : Finset α) (P : α → WordPolynomial 𝕜 I)
    (z : PolynomialTensor 𝕜 I) : tensorRight (∑ i ∈ S, P i) z = ∑ i ∈ S, tensorRight (P i) z := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih => simp [ha, tensorRight_add, ih]

private theorem tensorRight_mul' (P Q : WordPolynomial 𝕜 I) (z : PolynomialTensor 𝕜 I) :
    tensorRight (P * Q) z = tensorRight Q (tensorRight P z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b => simp [mul_assoc]
  | add x y hx hy => simp [map_add, hx, hy]

/-- Left matrix action is the actual associative bimodule action. -/
theorem matrixTensorLeft_mul (P Q : Matrix n n (WordPolynomial 𝕜 I))
    (Z : Matrix n n (PolynomialTensor 𝕜 I)) :
    matrixTensorLeft (P * Q) Z = matrixTensorLeft P (matrixTensorLeft Q Z) := by
  ext r c
  change (∑ u, tensorLeft ((P * Q) r u) (Z u c)) =
    ∑ v, tensorLeft (P r v) (∑ u, tensorLeft (Q v u) (Z u c))
  simp only [Matrix.mul_apply, tensorLeft_sum, map_sum, tensorLeft_mul]
  rw [Finset.sum_comm]

/-- Right matrix action is associative in the expected reversed operator order. -/
theorem matrixTensorRight_mul (P Q : Matrix n n (WordPolynomial 𝕜 I))
    (Z : Matrix n n (PolynomialTensor 𝕜 I)) :
    matrixTensorRight (P * Q) Z = matrixTensorRight Q (matrixTensorRight P Z) := by
  ext r c
  change (∑ u, tensorRight ((P * Q) u c) (Z r u)) =
    ∑ v, tensorRight (Q v c) (∑ u, tensorRight (P u v) (Z r u))
  simp only [Matrix.mul_apply, tensorRight_sum, map_sum, tensorRight_mul']
  rw [Finset.sum_comm]

/-- The first- and second-factor matrix actions commute. -/
theorem matrixTensorLeft_right (P Q : Matrix n n (WordPolynomial 𝕜 I))
    (Z : Matrix n n (PolynomialTensor 𝕜 I)) :
    matrixTensorLeft P (matrixTensorRight Q Z) = matrixTensorRight Q (matrixTensorLeft P Z) := by
  ext r c
  change (∑ u, tensorLeft (P r u) (∑ v, tensorRight (Q v c) (Z u v))) =
    ∑ v, tensorRight (Q v c) (∑ u, tensorLeft (P r u) (Z u v))
  simp only [map_sum, tensorLeft_right]
  rw [Finset.sum_comm]

@[simp] theorem matrixTensorLeft_one [DecidableEq n] (Z : Matrix n n (PolynomialTensor 𝕜 I)) :
    matrixTensorLeft 1 Z = Z := by
  ext r c
  change (∑ u, tensorLeft ((1 : Matrix n n (WordPolynomial 𝕜 I)) r u) (Z u c)) = Z r c
  simp [Matrix.one_apply, apply_ite, ite_apply]

@[simp] theorem matrixTensorRight_one [DecidableEq n] (Z : Matrix n n (PolynomialTensor 𝕜 I)) :
    matrixTensorRight 1 Z = Z := by
  ext r c
  change (∑ u, tensorRight ((1 : Matrix n n (WordPolynomial 𝕜 I)) u c) (Z r u)) = Z r c
  simp [Matrix.one_apply, apply_ite, ite_apply]

/-- The existing matrix free difference quotient is a derivation into this
actual tensor bimodule, with the declared matrix multiplication actions. -/
theorem matrixFreeDifferenceQuotient_leibniz (i : I) (P Q : Matrix n n (WordPolynomial 𝕜 I)) :
    matrixFreeDifferenceQuotient i (P * Q) =
      matrixTensorLeft P (matrixFreeDifferenceQuotient i Q) +
        matrixTensorRight Q (matrixFreeDifferenceQuotient i P) := by
  ext r c
  exact matrixFreeDifferenceQuotient_mul i P Q r c

end FreeProbability

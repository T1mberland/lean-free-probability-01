import FreeProbability.Matrix.RankOneSecular

/-!
# Exact algebra of triangular matrix products

Products of explicit triangular blocks and their Gram rank-one
representations are proved by matrix algebra.
-/

namespace FreeProbability.ReLU

open Matrix

variable {n : Type*} [Fintype n]

/-- A triangular block with a distinguished scalar coordinate. -/
def triangularMatrix (B : Matrix n n ℝ) (d : n → ℝ) (a : ℝ) :
    Matrix (n ⊕ Unit) (n ⊕ Unit) ℝ :=
  fromBlocks B 0 (replicateRow Unit d) (a • (1 : Matrix Unit Unit ℝ))

/-- Bulk Gram matrix extended by zero on the exceptional direction. -/
def bulkGram (C : Matrix n n ℝ) : Matrix (n ⊕ Unit) (n ⊕ Unit) ℝ :=
  fromBlocks (Cᵀ * C) 0 0 0

def exceptionalVector (c : n → ℝ) (a : ℝ) : n ⊕ Unit → ℝ := Sum.elim c (fun _ => a)

/-- Multiplication preserves triangular form with the exact cavity-row recurrence. -/
theorem triangularMatrix_mul (B C : Matrix n n ℝ) (d c : n → ℝ) (a b : ℝ) :
    triangularMatrix B d a * triangularMatrix C c b =
      triangularMatrix (B * C) (d ᵥ* C + a • c) (a * b) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [triangularMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.vecMul, dotProduct]

/-- The Gram matrix is exactly a positive rank-one deformation of the bulk block. -/
theorem triangularMatrix_gram (C : Matrix n n ℝ) (c : n → ℝ) (a : ℝ) :
    (triangularMatrix C c a)ᵀ * triangularMatrix C c a = bulkGram C +
      vecMulVec (exceptionalVector c a) (exceptionalVector c a) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [triangularMatrix, bulkGram, exceptionalVector, Matrix.mul_apply,
      Matrix.transpose_apply, Fintype.sum_sum_type,
      Matrix.vecMulVec_apply]

/-- The three pieces of a triangular Jacobian block. -/
structure TriangularData (n : Type*) where
  bulk : Matrix n n ℝ
  cavity : n → ℝ
  forward : ℝ

namespace TriangularData

def matrix (X : TriangularData n) := triangularMatrix X.bulk X.cavity X.forward

def compose (X Y : TriangularData n) : TriangularData n :=
  ⟨X.bulk * Y.bulk, X.cavity ᵥ* Y.bulk + X.forward • Y.cavity, X.forward * Y.forward⟩

@[simp] theorem matrix_compose (X Y : TriangularData n) :
    (X.compose Y).matrix = X.matrix * Y.matrix :=
  (triangularMatrix_mul _ _ _ _ _ _).symm

variable [DecidableEq n]

def identity : TriangularData n := ⟨1, 0, 1⟩

omit [Fintype n] in
@[simp] theorem matrix_identity : (identity : TriangularData n).matrix = 1 := by
  simp [identity, matrix, triangularMatrix]

/-- The list is in matrix multiplication order, with the rightmost block acting first. -/
def product (layers : List (TriangularData n)) : TriangularData n :=
  layers.foldr compose identity

@[simp] theorem matrix_product (layers : List (TriangularData n)) :
    (product layers).matrix = (layers.map matrix).prod := by
  induction layers with
  | nil => exact matrix_identity
  | cons X layers ih =>
      change (X.compose (product layers)).matrix = _
      rw [matrix_compose, ih]
      rfl

theorem forward_product (layers : List (TriangularData n)) :
    (product layers).forward = (layers.map forward).prod := by
  induction layers with
  | nil => rfl
  | cons X layers ih =>
      change X.forward * (product layers).forward = X.forward * (layers.map forward).prod
      rw [ih]

theorem bulk_product (layers : List (TriangularData n)) :
    (product layers).bulk = (layers.map bulk).prod := by
  induction layers with
  | nil => rfl
  | cons X layers ih =>
      change X.bulk * (product layers).bulk = X.bulk * (layers.map bulk).prod
      rw [ih]

/-- The triangular product's bottom row as an explicit sum over all layer positions.
Left-prefix forward scalars multiply each defect transported through the right suffix. -/
theorem cavity_product (layers : List (TriangularData n)) :
    (product layers).cavity = ∑ k : Fin layers.length,
      ((layers.take k.val).map forward).prod •
        ((layers.get k).cavity ᵥ* ((layers.drop (k.val + 1)).map bulk).prod) := by
  induction layers with
  | nil => simp [product, identity]
  | cons X layers ih =>
      change X.cavity ᵥ* (product layers).bulk + X.forward • (product layers).cavity = _
      rw [bulk_product, ih]
      conv_rhs =>
        change ∑ k : Fin (layers.length + 1),
          (((X :: layers).take k.val).map forward).prod •
            (((X :: layers).get k).cavity ᵥ* (((X :: layers).drop (k.val + 1)).map bulk).prod)
      rw [Fin.sum_univ_succ]
      simp [List.get_eq_getElem, List.take_succ_cons, List.drop_succ_cons,
        smul_smul, Finset.smul_sum]

/-- Arbitrary finite products have the exact Gram rank-one representation. -/
theorem product_gram (layers : List (TriangularData n)) :
    ((layers.map matrix).prod)ᵀ * (layers.map matrix).prod = bulkGram (product layers).bulk +
      vecMulVec (exceptionalVector (product layers).cavity (product layers).forward)
        (exceptionalVector (product layers).cavity (product layers).forward) := by
  rw [← matrix_product]
  exact triangularMatrix_gram _ _ _

end TriangularData

variable [DecidableEq n]

theorem bulkGram_shift (C : Matrix n n ℝ) (z : ℝ) :
    z • (1 : Matrix (n ⊕ Unit) (n ⊕ Unit) ℝ) - bulkGram C =
      fromBlocks (z • (1 : Matrix n n ℝ) - Cᵀ * C) 0 0 (z • (1 : Matrix Unit Unit ℝ)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [bulkGram, Matrix.one_apply]

theorem bulkGram_det_ne_zero (C : Matrix n n ℝ) (z : ℝ)
    (hC : (z • (1 : Matrix n n ℝ) - Cᵀ * C).det ≠ 0) (hz : z ≠ 0) :
    (z • (1 : Matrix (n ⊕ Unit) (n ⊕ Unit) ℝ) - bulkGram C).det ≠ 0 := by
  rw [bulkGram_shift, Matrix.det_fromBlocks_zero₂₁]
  simpa [Matrix.det_unique] using mul_ne_zero hC hz

theorem bulkGram_resolvent (C : Matrix n n ℝ) (z : ℝ)
    (hC : (z • (1 : Matrix n n ℝ) - Cᵀ * C).det ≠ 0) (hz : z ≠ 0) :
    (z • (1 : Matrix (n ⊕ Unit) (n ⊕ Unit) ℝ) - bulkGram C)⁻¹ =
      fromBlocks ((z • (1 : Matrix n n ℝ) - Cᵀ * C)⁻¹) 0 0
        (z⁻¹ • (1 : Matrix Unit Unit ℝ)) := by
  apply Matrix.inv_eq_right_inv
  rw [bulkGram_shift, Matrix.fromBlocks_multiply]
  simp [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hC),
    smul_smul, inv_mul_cancel₀ hz, Matrix.fromBlocks_one]

/-- Exact scalar cavity resolvent form, before any asymptotic argument. -/
noncomputable def cavitySecular (C : Matrix n n ℝ) (c : n → ℝ) (a z : ℝ) : ℝ :=
  c ⬝ᵥ (z • (1 : Matrix n n ℝ) - Cᵀ * C)⁻¹ *ᵥ c + a ^ 2 / z

theorem secular_bulkGram (C : Matrix n n ℝ) (c : n → ℝ) (a z : ℝ)
    (hC : (z • (1 : Matrix n n ℝ) - Cᵀ * C).det ≠ 0) (hz : z ≠ 0) :
    secular (bulkGram C) (exceptionalVector c a) (exceptionalVector c a) z =
      1 - cavitySecular C c a z := by
  unfold secular
  rw [bulkGram_resolvent C z hC hz]
  simp [cavitySecular, exceptionalVector, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, div_eq_mul_inv, pow_two, mul_comm, mul_assoc]

/-- The exact finite-dimensional secular eigenvalue equation for a triangular Gram matrix.
The bulk resolvent and scalar parameter are assumed invertible. -/
theorem triangularMatrix_secular_iff (C : Matrix n n ℝ) (c : n → ℝ) (a z : ℝ)
    (hC : (z • (1 : Matrix n n ℝ) - Cᵀ * C).det ≠ 0) (hz : z ≠ 0) :
    IsMatrixEigenvalue ((triangularMatrix C c a)ᵀ * triangularMatrix C c a) z ↔
      cavitySecular C c a z = 1 := by
  rw [triangularMatrix_gram, rankOne_isEigenvalue_iff _ _ _ _ (bulkGram_det_ne_zero C z hC hz),
    secular_bulkGram C c a z hC hz, sub_eq_zero]
  exact eq_comm

end FreeProbability.ReLU

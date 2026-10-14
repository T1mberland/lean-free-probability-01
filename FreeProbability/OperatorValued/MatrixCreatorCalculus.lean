import FreeProbability.OperatorValued.MatrixWordExpansion
import FreeProbability.OperatorValued.MatrixCauchyLyapunov

/-! # Actual matrix creation-operator Gram calculus

These identities use the genuine canonical creation operators. Arbitrary matrix
coefficients are allowed; their order is preserved in the creator Gram identity.
-/

noncomputable section
open scoped Classical
open Matrix
namespace FreeProbability.Fock

variable {I n : Type*} [Fintype I] [Fintype n] [DecidableEq n]

/-- Actual matrix linear combination of canonical creation operators. -/
def matrixCreationCombination (C : I → Matrix n n ℂ) : Matrix n n (WordSpace I →L[ℂ] WordSpace I) :=
  matrixLinearCombination creation C

/-- Actual matrix linear combination of canonical annihilation operators. -/
def matrixAnnihilationCombination (C : I → Matrix n n ℂ) : Matrix n n (WordSpace I →L[ℂ] WordSpace I) :=
  matrixLinearCombination annihilation C

omit [Fintype n] [DecidableEq n] in
/-- Taking the true adjoint conjugates and transposes each matrix coefficient. -/
theorem matrixCreationCombination_conjTranspose (C : I → Matrix n n ℂ) :
    (matrixCreationCombination C)ᴴ = matrixAnnihilationCombination (fun i => (C i)ᴴ) := by
  apply Matrix.ext
  intro r c
  simp only [matrixCreationCombination, matrixAnnihilationCombination, matrixLinearCombination,
    Matrix.conjTranspose_apply, ContinuousLinearMap.star_eq_adjoint, annihilation, map_sum, map_smulₛₗ, starRingEnd_apply]

omit [Fintype I] in
private theorem annihilation_mul_creation (i j : I) :
    annihilation i * creation j = if i = j then (1 : WordSpace I →L[ℂ] WordSpace I) else 0 :=
  annihilation_creation i j

/-- Genuine matrix creation operators contract their full coefficient Gram
matrix, with no Hermitian-coefficient assumption. -/
theorem matrixCreationCombination_gram (C D : I → Matrix n n ℂ) :
    (matrixCreationCombination C)ᴴ * matrixCreationCombination D =
      scalarMatrixEmbedding (∑ i, (C i)ᴴ * D i) := by
  rw [matrixCreationCombination_conjTranspose]
  apply Matrix.ext
  intro r c
  simp only [Matrix.mul_apply, matrixAnnihilationCombination, matrixCreationCombination,
    matrixLinearCombination, Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, smul_smul, annihilation_mul_creation, smul_ite,
    smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [scalarMatrixEmbedding_apply, Matrix.sum_apply, map_sum]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum,
    Algebra.algebraMap_eq_smul_one]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro u _
  rw [mul_comm]

omit [Fintype n] [DecidableEq n] in
/-- Canonical semicircular matrix combinations are exactly creation plus annihilation. -/
theorem matrixLinearCombination_semicircular_eq (C : I → Matrix n n ℂ) :
    matrixLinearCombination semicircular C = matrixCreationCombination C + matrixAnnihilationCombination C := by
  apply Matrix.ext
  intro r c
  simp [matrixLinearCombination, semicircular, matrixCreationCombination, matrixAnnihilationCombination,
    smul_add, Finset.sum_add_distrib]

end FreeProbability.Fock

import FreeProbability.OperatorValued.MatrixLinearCombination
import FreeProbability.Fock.FreeCStarModel

/-!
# The actual finite-matrix Fock semicircular model

The entries are the constructed semicircular operators in their faithful tracial
generated C-star algebra. Centering and the exact coefficient covariance are
derived from these actual operators, not supplied as moment assumptions.
This is the finite-matrix case; arbitrary base-algebra covariance realization
and the resolvent/Dyson identities are separate developments.
-/

noncomputable section
open scoped Classical

namespace FreeProbability.Fock

open Matrix

variable {I n : Type*} [Fintype I] [Fintype n] [DecidableEq n]

/-- The genuine matrix over the actual Fock semicircular C-star algebra. -/
def closedMatrixSemicircular (C : I → Matrix n n ℂ) : Matrix n n (closedSemicircularAlgebra I) :=
  matrixLinearCombination closedSemicircular C

/-- An affine Hermitian matrix pencil with actual Fock semicircular entries. -/
def closedMatrixPencil (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ) :
    Matrix n n (closedSemicircularAlgebra I) :=
  scalarMatrixEmbedding C₀ + closedMatrixSemicircular C

omit [Fintype I] in
/-- The genuine canonical scalar covariance is the Kronecker covariance. -/
theorem closedGeneratedVacuumState_second (i j : I) :
    (closedGeneratedVacuumState I).expectation (closedSemicircular i * closedSemicircular j) =
      if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simpa only [← pow_two, ite_true] using closedGeneratedVacuumState_variance_one i
  · rw [(freelyIndependent_closedGeneratedVacuumState I).expectation_mul hij
      (closedSemicircular_mem_closedGeneratorAlgebra i) (closedSemicircular_mem_closedGeneratorAlgebra j),
      closedGeneratedVacuumState_centered, closedGeneratedVacuumState_centered]
    simp only [hij, ite_false, mul_zero]

omit [Fintype n] [DecidableEq n] in
/-- Centering of the actual matrix-valued random variable. -/
theorem closedMatrixSemicircular_centered (C : I → Matrix n n ℂ) :
    matrixExpectation (closedGeneratedVacuumState I).toProbabilitySpace (closedMatrixSemicircular C) = 0 :=
  matrixExpectation_linearCombination_centered _ _ C closedGeneratedVacuumState_centered

omit [Fintype n] [DecidableEq n] in
/-- Self-adjointness of the actual matrix model for arbitrary Hermitian coefficients. -/
theorem closedMatrixSemicircular_isHermitian (C : I → Matrix n n ℂ)
    (hC : ∀ i, (C i).IsHermitian) : (closedMatrixSemicircular C).IsHermitian :=
  matrixLinearCombination_isHermitian _ C (fun i => (isSelfAdjoint_closedSemicircular i).star_eq) hC

/-- Exact operator-valued covariance of the constructed matrix Fock variable,
for every coefficient matrix `D`. -/
theorem closedMatrixSemicircular_covariance (C : I → Matrix n n ℂ) (D : Matrix n n ℂ) :
    matrixExpectation (closedGeneratedVacuumState I).toProbabilitySpace
      (closedMatrixSemicircular C * scalarMatrixEmbedding D * closedMatrixSemicircular C) =
        matrixCovariance C D :=
  matrixExpectation_linearCombination_covariance _ _ C closedGeneratedVacuumState_second D

/-- The same covariance in the actual range-target conditional-expectation interface. -/
theorem closedMatrixSemicircular_conditional_covariance (C : I → Matrix n n ℂ) (D : Matrix n n ℂ) :
    ((matrixConditionalExpectation (closedGeneratedVacuumState I).toProbabilitySpace).toLinearMap
      (closedMatrixSemicircular C * scalarMatrixEmbedding D * closedMatrixSemicircular C) :
        Matrix n n (closedSemicircularAlgebra I)) = scalarMatrixEmbedding (matrixCovariance C D) := by
  rw [matrixConditionalExpectation_coe, closedMatrixSemicircular_covariance]

/-- The affine pencil has exactly its deterministic coefficient as its mean. -/
theorem closedMatrixPencil_expectation (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ) :
    matrixExpectation (closedGeneratedVacuumState I).toProbabilitySpace (closedMatrixPencil C₀ C) = C₀ := by
  simp only [closedMatrixPencil, map_add, matrixExpectation_scalarMatrixEmbedding,
    closedMatrixSemicircular_centered, add_zero]

end FreeProbability.Fock

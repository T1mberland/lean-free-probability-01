import FreeProbability.OperatorValued.MatrixResolventBoundary
import FreeProbability.Analytic.FockResolventIntegrationByParts
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Actual finite matrix Fock resolvent integration by parts -/

noncomputable section
open scoped Classical CStarAlgebra
namespace FreeProbability.Fock

variable {I n : Type*} [Fintype I] [Fintype n] [DecidableEq n]

local instance : PartialOrder (WordSpace I →L[ℂ] WordSpace I) := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing (WordSpace I →L[ℂ] WordSpace I) :=
  CStarAlgebra.spectralOrderedRing _

/-- The genuine matrix Fock operator with its C-star operator norm. -/
def operatorMatrixSemicircular (C : I → Matrix n n ℂ) :
    CStarMatrix n n (WordSpace I →L[ℂ] WordSpace I) :=
  CStarMatrix.ofMatrix (matrixLinearCombination semicircular C)

/-- The actual inverse resolvent matrix, retaining its bounded-operator entries. -/
def operatorMatrixResolvent (C : I → Matrix n n ℂ) (z : ℂ) :
    Matrix n n (WordSpace I →L[ℂ] WordSpace I) :=
  CStarMatrix.ofMatrix.symm (resolvent (operatorMatrixSemicircular C) z)

/-- Entrywise vacuum expectation of the actual matrix resolvent. -/
def operatorMatrixCauchy (C : I → Matrix n n ℂ) (z : ℂ) : Matrix n n ℂ :=
  matrixExpectation (vacuumState I).toProbabilitySpace (operatorMatrixResolvent C z)

/-- The inverse boundary identity holds at every genuine matrix resolvent point. -/
theorem operatorMatrixResolvent_boundary (i : I) (C : I → Matrix n n ℂ) (z : ℂ)
    (hz : z ∈ resolventSet ℂ (operatorMatrixSemicircular C)) :
    matrixRightAnnihilation i * operatorMatrixResolvent C z -
      operatorMatrixResolvent C z * matrixRightAnnihilation i =
      operatorMatrixResolvent C z * scalarMatrixEmbedding (C i) *
        Matrix.diagonal (fun _ : n => vacuumProjection) * operatorMatrixResolvent C z := by
  let N : CStarMatrix n n (WordSpace I →L[ℂ] WordSpace I) :=
    CStarMatrix.ofMatrix (matrixRightAnnihilation i)
  have hc : N * operatorMatrixSemicircular C - operatorMatrixSemicircular C * N =
      CStarMatrix.ofMatrix (scalarMatrixEmbedding (C i) *
        Matrix.diagonal (fun _ : n => vacuumProjection)) :=
    congrArg CStarMatrix.ofMatrix (matrixRightAnnihilation_linearCombination_commutator i C)
  have h := commutator_inverse_unit N hz.unit
  rw [← spectrum.resolvent_eq hz, hz.unit_spec] at h
  have hb : (algebraMap ℂ _ z - operatorMatrixSemicircular C) * N -
      N * (algebraMap ℂ _ z - operatorMatrixSemicircular C) =
      N * operatorMatrixSemicircular C - operatorMatrixSemicircular C * N := by
    simp only [sub_mul, mul_sub, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    abel
  rw [hb, hc] at h
  change CStarMatrix.ofMatrix
    (matrixRightAnnihilation i * operatorMatrixResolvent C z -
      operatorMatrixResolvent C z * matrixRightAnnihilation i) =
      CStarMatrix.ofMatrix (operatorMatrixResolvent C z *
        (scalarMatrixEmbedding (C i) * Matrix.diagonal (fun _ : n => vacuumProjection)) *
          operatorMatrixResolvent C z) at h
  exact (CStarMatrix.ofMatrix.injective h).trans (by simp only [mul_assoc])

/-- Actual matrix resolvent IBP, with no formal-series or convergence premise. -/
theorem operatorMatrixResolvent_integrationByParts (i : I) (C : I → Matrix n n ℂ) (z : ℂ)
    (hz : z ∈ resolventSet ℂ (operatorMatrixSemicircular C)) :
    matrixExpectation (vacuumState I).toProbabilitySpace
      (Matrix.diagonal (fun _ : n => semicircular i) * operatorMatrixResolvent C z) =
      operatorMatrixCauchy C z * C i * operatorMatrixCauchy C z := by
  rw [← matrixVacuumExpectation_rightAnnihilation_commutator,
    operatorMatrixResolvent_boundary i C z hz, matrixVacuumExpectation_mul_projection_mul]
  rfl

/-- The covariance identity for the actual resolvent at every invertibility point. -/
theorem operatorMatrixResolvent_covariance (C : I → Matrix n n ℂ) (z : ℂ)
    (hz : z ∈ resolventSet ℂ (operatorMatrixSemicircular C)) :
    matrixExpectation (vacuumState I).toProbabilitySpace
      (matrixLinearCombination semicircular C * operatorMatrixResolvent C z) =
      matrixCovariance C (operatorMatrixCauchy C z) * operatorMatrixCauchy C z := by
  rw [matrixLinearCombination_eq_sum, Finset.sum_mul, map_sum, matrixCovariance_apply,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_assoc, matrixExpectation_mul_left, operatorMatrixResolvent_integrationByParts i C z hz]
  simp only [mul_assoc]

/-- The actual matrix Cauchy transform satisfies Dyson's equation at every
actual resolvent point, without a convergence or analytic-continuation premise. -/
theorem operatorMatrixCauchy_dyson (C : I → Matrix n n ℂ) (z : ℂ)
    (hz : z ∈ resolventSet ℂ (operatorMatrixSemicircular C)) :
    (z • (1 : Matrix n n ℂ) - matrixCovariance C (operatorMatrixCauchy C z)) *
      operatorMatrixCauchy C z = 1 := by
  have hr : (algebraMap ℂ _ z - operatorMatrixSemicircular C) *
      resolvent (operatorMatrixSemicircular C) z = 1 := Ring.mul_inverse_cancel _ hz
  simp only [Algebra.algebraMap_eq_smul_one] at hr
  change CStarMatrix.ofMatrix
    ((z • (1 : Matrix n n (WordSpace I →L[ℂ] WordSpace I)) -
      matrixLinearCombination semicircular C) * operatorMatrixResolvent C z) =
        CStarMatrix.ofMatrix 1 at hr
  have he := congrArg (matrixExpectation (vacuumState I).toProbabilitySpace)
    (CStarMatrix.ofMatrix.injective hr)
  have hunit : matrixExpectation (vacuumState I).toProbabilitySpace
      (1 : Matrix n n (WordSpace I →L[ℂ] WordSpace I)) = 1 := by
    simpa using matrixExpectation_scalarMatrixEmbedding (vacuumState I).toProbabilitySpace
      (1 : Matrix n n ℂ)
  have hscale : (z • (1 : Matrix n n (WordSpace I →L[ℂ] WordSpace I))) *
      operatorMatrixResolvent C z = z • operatorMatrixResolvent C z := by
    exact (Matrix.smul_mul z 1 (operatorMatrixResolvent C z)).trans (by rw [one_mul])
  rw [sub_mul, hscale, map_sub, map_smul, hunit] at he
  rw [operatorMatrixResolvent_covariance C z hz] at he
  simpa only [sub_mul, Matrix.smul_mul, one_mul, operatorMatrixCauchy] using he

/-- The actual resolvent expectation is invertible as a finite complex matrix. -/
theorem operatorMatrixCauchy_isUnit (C : I → Matrix n n ℂ) (z : ℂ)
    (hz : z ∈ resolventSet ℂ (operatorMatrixSemicircular C)) :
    IsUnit (operatorMatrixCauchy C z) := by
  apply (Matrix.isUnit_iff_isUnit_det (operatorMatrixCauchy C z)).mpr
  apply isUnit_of_mul_isUnit_right (x :=
    (z • (1 : Matrix n n ℂ) - matrixCovariance C (operatorMatrixCauchy C z)).det)
  rw [← Matrix.det_mul, operatorMatrixCauchy_dyson C z hz, Matrix.det_one]
  exact isUnit_one

/-- Dyson's inverse form uses the actual Cauchy transform's matrix inverse;
finite-dimensional right-inverse cancellation supplies invertibility. -/
theorem operatorMatrixCauchy_inverse_dyson (C : I → Matrix n n ℂ) (z : ℂ)
    (hz : z ∈ resolventSet ℂ (operatorMatrixSemicircular C)) :
    (operatorMatrixCauchy C z)⁻¹ = z • (1 : Matrix n n ℂ) -
      matrixCovariance C (operatorMatrixCauchy C z) :=
  Matrix.inv_eq_left_inv (operatorMatrixCauchy_dyson C z hz)

omit [Fintype n] [DecidableEq n] in
/-- Hermitian coefficient matrices give a genuine self-adjoint C-star matrix. -/
theorem operatorMatrixSemicircular_isSelfAdjoint (C : I → Matrix n n ℂ)
    (hC : ∀ i, (C i).IsHermitian) : IsSelfAdjoint (operatorMatrixSemicircular C) := by
  change CStarMatrix.ofMatrix (matrixLinearCombination semicircular C).conjTranspose =
    CStarMatrix.ofMatrix (matrixLinearCombination semicircular C)
  exact congrArg CStarMatrix.ofMatrix
    (matrixLinearCombination_isHermitian semicircular C
      (fun i => (isSelfAdjoint_semicircular i).star_eq) hC).eq

/-- For Hermitian coefficients the actual matrix resolvent and Dyson equation
are available at every nonreal argument. -/
theorem operatorMatrixCauchy_inverse_dyson_nonreal (C : I → Matrix n n ℂ)
    (hC : ∀ i, (C i).IsHermitian) (z : ℂ) (hz : z.im ≠ 0) :
    (operatorMatrixCauchy C z)⁻¹ = z • (1 : Matrix n n ℂ) -
      matrixCovariance C (operatorMatrixCauchy C z) :=
  operatorMatrixCauchy_inverse_dyson C z
    (StarProbabilitySpace.selfAdjoint_mem_resolventSet_of_im_ne_zero (operatorMatrixSemicircular C)
      (operatorMatrixSemicircular_isSelfAdjoint C hC) z hz)

end FreeProbability.Fock

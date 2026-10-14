import FreeProbability.OperatorValued.MatrixResolventDyson

/-! # Genuine operator-valued matrix-argument Dyson equation

The argument is an arbitrary deterministic complex matrix. The domain premise
is exactly invertibility of the embedded argument minus the actual Fock matrix.
-/

noncomputable section
open scoped Classical
namespace FreeProbability.Fock

variable {I n : Type*} [Fintype I] [Fintype n] [DecidableEq n]

/-- The true operator difference at a deterministic matrix argument. -/
def operatorMatrixDifference (C : I → Matrix n n ℂ) (B : Matrix n n ℂ) :
    CStarMatrix n n (WordSpace I →L[ℂ] WordSpace I) :=
  CStarMatrix.ofMatrix (scalarMatrixEmbedding B - matrixLinearCombination semicircular C)

/-- The actual inverse of the matrix-argument operator difference. -/
def operatorMatrixArgumentResolvent (C : I → Matrix n n ℂ) (B : Matrix n n ℂ) :
    Matrix n n (WordSpace I →L[ℂ] WordSpace I) :=
  CStarMatrix.ofMatrix.symm (Ring.inverse (operatorMatrixDifference C B))

/-- Actual operator-valued Cauchy transform at a deterministic matrix argument. -/
def operatorMatrixArgumentCauchy (C : I → Matrix n n ℂ) (B : Matrix n n ℂ) : Matrix n n ℂ :=
  matrixExpectation (vacuumState I).toProbabilitySpace (operatorMatrixArgumentResolvent C B)

omit [Fintype I] in
private theorem commutator_ringInverse (N X : CStarMatrix n n (WordSpace I →L[ℂ] WordSpace I))
    (hX : IsUnit X) : N * Ring.inverse X - Ring.inverse X * N =
      Ring.inverse X * (X * N - N * X) * Ring.inverse X := by
  obtain ⟨u, rfl⟩ := hX
  simpa only [Ring.inverse_unit] using commutator_inverse_unit N u

omit [Fintype I] in
/-- Scalar coefficient matrices commute with the amplified boundary operator. -/
theorem matrixRightAnnihilation_coefficient_commute (i : I) (B : Matrix n n ℂ) :
    matrixRightAnnihilation i * scalarMatrixEmbedding B =
      scalarMatrixEmbedding B * matrixRightAnnihilation i := by
  apply Matrix.ext
  intro r c
  simp only [matrixRightAnnihilation, Matrix.diagonal_mul, Matrix.mul_diagonal,
    scalarMatrixEmbedding_apply]
  exact (Algebra.commutes (B r c) (rightAnnihilation i)).symm

/-- Exact inverse boundary derivative for arbitrary deterministic matrix arguments. -/
theorem operatorMatrixArgumentResolvent_boundary (i : I) (C : I → Matrix n n ℂ)
    (B : Matrix n n ℂ) (hB : IsUnit (operatorMatrixDifference C B)) :
    matrixRightAnnihilation i * operatorMatrixArgumentResolvent C B -
      operatorMatrixArgumentResolvent C B * matrixRightAnnihilation i =
      operatorMatrixArgumentResolvent C B * scalarMatrixEmbedding (C i) *
        Matrix.diagonal (fun _ : n => vacuumProjection) * operatorMatrixArgumentResolvent C B := by
  let N : CStarMatrix n n (WordSpace I →L[ℂ] WordSpace I) :=
    CStarMatrix.ofMatrix (matrixRightAnnihilation i)
  have hc : operatorMatrixDifference C B * N - N * operatorMatrixDifference C B =
      CStarMatrix.ofMatrix (scalarMatrixEmbedding (C i) *
        Matrix.diagonal (fun _ : n => vacuumProjection)) := by
    apply CStarMatrix.ofMatrix.injective.eq_iff.mpr
    change (scalarMatrixEmbedding B - matrixLinearCombination semicircular C) * matrixRightAnnihilation i -
      matrixRightAnnihilation i * (scalarMatrixEmbedding B - matrixLinearCombination semicircular C) = _
    rw [sub_mul, mul_sub, matrixRightAnnihilation_coefficient_commute]
    calc
      _ = matrixRightAnnihilation i * matrixLinearCombination semicircular C -
          matrixLinearCombination semicircular C * matrixRightAnnihilation i := by abel
      _ = _ := matrixRightAnnihilation_linearCombination_commutator i C
  have h := commutator_ringInverse N (operatorMatrixDifference C B) hB
  rw [hc] at h
  change CStarMatrix.ofMatrix
    (matrixRightAnnihilation i * operatorMatrixArgumentResolvent C B -
      operatorMatrixArgumentResolvent C B * matrixRightAnnihilation i) =
      CStarMatrix.ofMatrix (operatorMatrixArgumentResolvent C B *
        (scalarMatrixEmbedding (C i) * Matrix.diagonal (fun _ : n => vacuumProjection)) *
          operatorMatrixArgumentResolvent C B) at h
  exact (CStarMatrix.ofMatrix.injective h).trans (by simp only [mul_assoc])

/-- Actual inverse integration by parts for every invertible matrix argument. -/
theorem operatorMatrixArgumentResolvent_integrationByParts (i : I) (C : I → Matrix n n ℂ)
    (B : Matrix n n ℂ) (hB : IsUnit (operatorMatrixDifference C B)) :
    matrixExpectation (vacuumState I).toProbabilitySpace
      (Matrix.diagonal (fun _ : n => semicircular i) * operatorMatrixArgumentResolvent C B) =
      operatorMatrixArgumentCauchy C B * C i * operatorMatrixArgumentCauchy C B := by
  rw [← matrixVacuumExpectation_rightAnnihilation_commutator,
    operatorMatrixArgumentResolvent_boundary i C B hB, matrixVacuumExpectation_mul_projection_mul]
  rfl

/-- Exact covariance contraction of the actual inverse. -/
theorem operatorMatrixArgumentResolvent_covariance (C : I → Matrix n n ℂ)
    (B : Matrix n n ℂ) (hB : IsUnit (operatorMatrixDifference C B)) :
    matrixExpectation (vacuumState I).toProbabilitySpace
      (matrixLinearCombination semicircular C * operatorMatrixArgumentResolvent C B) =
      matrixCovariance C (operatorMatrixArgumentCauchy C B) * operatorMatrixArgumentCauchy C B := by
  rw [matrixLinearCombination_eq_sum, Finset.sum_mul, map_sum, matrixCovariance_apply,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_assoc, matrixExpectation_mul_left, operatorMatrixArgumentResolvent_integrationByParts i C B hB]
  simp only [mul_assoc]

/-- The true operator-valued matrix Cauchy transform obeys Dyson at every
invertible deterministic matrix argument. -/
theorem operatorMatrixArgumentCauchy_dyson (C : I → Matrix n n ℂ)
    (B : Matrix n n ℂ) (hB : IsUnit (operatorMatrixDifference C B)) :
    (B - matrixCovariance C (operatorMatrixArgumentCauchy C B)) * operatorMatrixArgumentCauchy C B = 1 := by
  have hr := Ring.mul_inverse_cancel _ hB
  change CStarMatrix.ofMatrix
    ((scalarMatrixEmbedding B - matrixLinearCombination semicircular C) *
      operatorMatrixArgumentResolvent C B) = CStarMatrix.ofMatrix 1 at hr
  have he := congrArg (matrixExpectation (vacuumState I).toProbabilitySpace)
    (CStarMatrix.ofMatrix.injective hr)
  have hunit : matrixExpectation (vacuumState I).toProbabilitySpace
      (1 : Matrix n n (WordSpace I →L[ℂ] WordSpace I)) = 1 := by
    simpa using matrixExpectation_scalarMatrixEmbedding (vacuumState I).toProbabilitySpace
      (1 : Matrix n n ℂ)
  rw [sub_mul, map_sub, matrixExpectation_mul_left,
    operatorMatrixArgumentResolvent_covariance C B hB, hunit] at he
  simpa only [sub_mul, operatorMatrixArgumentCauchy] using he

/-- The actual matrix-argument Cauchy transform is an invertible complex matrix. -/
theorem operatorMatrixArgumentCauchy_isUnit (C : I → Matrix n n ℂ)
    (B : Matrix n n ℂ) (hB : IsUnit (operatorMatrixDifference C B)) :
    IsUnit (operatorMatrixArgumentCauchy C B) := by
  apply (Matrix.isUnit_iff_isUnit_det (operatorMatrixArgumentCauchy C B)).mpr
  apply isUnit_of_mul_isUnit_right (x :=
    (B - matrixCovariance C (operatorMatrixArgumentCauchy C B)).det)
  rw [← Matrix.det_mul, operatorMatrixArgumentCauchy_dyson C B hB, Matrix.det_one]
  exact isUnit_one

/-- Inverse form of the actual matrix-argument Dyson equation. -/
theorem operatorMatrixArgumentCauchy_inverse_dyson (C : I → Matrix n n ℂ)
    (B : Matrix n n ℂ) (hB : IsUnit (operatorMatrixDifference C B)) :
    (operatorMatrixArgumentCauchy C B)⁻¹ = B - matrixCovariance C (operatorMatrixArgumentCauchy C B) :=
  Matrix.inv_eq_left_inv (operatorMatrixArgumentCauchy_dyson C B hB)

end FreeProbability.Fock

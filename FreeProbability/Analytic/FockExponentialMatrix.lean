import FreeProbability.Analytic.FockExponentialPolynomial
import FreeProbability.Fock.MatrixPolynomialIntegrationByParts
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.UniformSpace.Matrix

/-!
# Actual finite-matrix polynomial exponential integration by parts

Finite matrices use the genuine Banach algebra `L∞` operator norm; this norm is
not asserted to be a C-star norm. Duhamel's identity is applied to actual matrix
multiplication and its convergent matrix exponential. The amplified vacuum
expectation is entrywise, and the FDQ contraction retains both matrix indices.
-/

noncomputable section
open scoped Classical Matrix.Norms.Operator
open NormedSpace

namespace FreeProbability.Fock

variable {I N : Type*} [Fintype N] [DecidableEq N]

local instance : NormedAddCommGroup (Matrix N N (WordSpace I →L[ℂ] WordSpace I)) :=
  { Matrix.linftyOpNormedRing (α := WordSpace I →L[ℂ] WordSpace I) (n := N) with }

/-- The Banach matrix ring retains the complete product uniformity. -/
local instance : @CompleteSpace (Matrix N N (WordSpace I →L[ℂ] WordSpace I))
    (Matrix.linftyOpNormedRing.toUniformSpace) := by
  change CompleteSpace (N → N → (WordSpace I →L[ℂ] WordSpace I))
  infer_instance

/-- A continuous entry of the actual amplified vacuum expectation. -/
def matrixEntryVacuum (r c : N) : Matrix N N (WordSpace I →L[ℂ] WordSpace I) →L[ℂ] ℂ where
  toLinearMap :=
    { toFun := fun X => vacuumExpectation (X r c)
      map_add' := fun X Y => (vacuumLinear (I := I)).map_add (X r c) (Y r c)
      map_smul' := fun t X => (vacuumLinear (I := I)).map_smul t (X r c) }
  cont := (vacuumContinuous I).continuous.comp (continuous_apply_apply r c)

/-- Every entry of the amplified boundary commutator is the actual polynomial FDQ insertion. -/
theorem matrix_polynomial_commutator (i : I) (P : Matrix N N (WordPolynomial ℂ I)) (t : ℂ) :
    Matrix.diagonal (fun _ : N => rightAnnihilation i) *
        (t • matrixPolynomialEvaluate semicircular P) -
      (t • matrixPolynomialEvaluate semicircular P) *
        Matrix.diagonal (fun _ : N => rightAnnihilation i) =
      fun r c => t • polynomialRankOneInsertion (matrixFreeDifferenceQuotient i P r c) := by
  apply Matrix.ext
  intro r c
  simp only [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.smul_apply, matrixPolynomialEvaluate, matrixFreeDifferenceQuotient]
  change operatorCommutator (rightAnnihilation i) (t • evaluate semicircular (P r c)) = _
  rw [map_smul, rightAnnihilation_polynomial_commutator]

/-- The actual ordered matrix sandwich contracts all FDQ entries with both matrix factors. -/
def matrixExponentialTensorContraction
    (L R : Matrix N N (WordSpace I →L[ℂ] WordSpace I))
    (Z : Matrix N N (PolynomialTensor ℂ I)) (r c : N) : ℂ :=
  ∑ k, ∑ l, sandwichPolynomialExpectation (L r k) (R l c) (Z k l)

/-- Exact entire exponential IBP for arbitrary finite square matrix-valued polynomials.
The left side is the actual `id_M ⊗ τ` amplification, with actual matrix products
and an actual matrix exponential. The complex scalar parameter is unrestricted. -/
theorem vacuumState_matrix_polynomial_exp_integrationByParts
    (i : I) (P : Matrix N N (WordPolynomial ℂ I)) (t : ℂ) (r c : N) :
    ((Matrix.diagonal (fun _ : N => semicircular i) *
        exp (t • matrixPolynomialEvaluate semicircular P)).map vacuumExpectation) r c =
      t * (∫ u in (0 : ℝ)..1, matrixExponentialTensorContraction
        (exp ((1 - u) • (t • matrixPolynomialEvaluate semicircular P)))
        (exp (u • (t • matrixPolynomialEvaluate semicircular P)))
        (matrixFreeDifferenceQuotient i P) r c) := by
  let X := t • matrixPolynomialEvaluate semicircular P
  let C := Matrix.diagonal (fun _ : N => rightAnnihilation i)
  have hd := exponential_commutator_eq_integral C X
  have hi := (continuous_exponentialCommutatorIntegrand C X).intervalIntegrable
    (μ := MeasureTheory.volume) 0 1
  have he := congrArg (matrixEntryVacuum (I := I) r c) hd
  change matrixEntryVacuum (I := I) r c (C * exp X - exp X * C) =
    matrixEntryVacuum (I := I) r c (∫ u in (0 : ℝ)..1, exponentialCommutatorIntegrand C X u) at he
  have he' := he.trans ((matrixEntryVacuum (I := I) r c).intervalIntegral_comp_comm hi).symm
  clear he
  have he := he'
  clear he'
  change vacuumExpectation ((C * exp X - exp X * C) r c) =
    ∫ u in (0 : ℝ)..1, vacuumExpectation
      ((exp ((1 - u) • X) * (C * X - X * C) * exp (u • X)) r c) at he
  simp only [C, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal] at he
  rw [vacuumExpectation_rightAnnihilation_commutator] at he
  simp only [Matrix.map_apply, Matrix.diagonal_mul]
  change vacuumExpectation (semicircular i * (exp X) r c) = _
  rw [he]
  let B : Matrix N N (WordSpace I →L[ℂ] WordSpace I) :=
    fun k l => t • polynomialRankOneInsertion (matrixFreeDifferenceQuotient i P k l)
  have hb : C * X - X * C = B := matrix_polynomial_commutator i P t
  change (∫ u in (0 : ℝ)..1, vacuumLinear
    ((exp ((1 - u) • X) * (C * X - X * C) * exp (u • X)) r c)) = _
  simp_rw [hb]
  simp only [Matrix.mul_apply]
  simp only [B, Finset.sum_mul, map_sum, mul_smul_comm, smul_mul_assoc, map_smul]
  change (∫ u in (0 : ℝ)..1, ∑ l, ∑ k, t * vacuumExpectation
    ((exp ((1 - u) • X)) r k * polynomialRankOneInsertion (matrixFreeDifferenceQuotient i P k l) *
      (exp (u • X)) l c)) = _
  simp_rw [vacuumExpectation_sandwichRankOne]
  rw [show (fun u : ℝ => ∑ l, ∑ k, t * sandwichPolynomialExpectation
        ((exp ((1 - u) • X)) r k) ((exp (u • X)) l c)
        (matrixFreeDifferenceQuotient i P k l)) =
      (fun u : ℝ => t * matrixExponentialTensorContraction
        (exp ((1 - u) • X)) (exp (u • X)) (matrixFreeDifferenceQuotient i P) r c) by
      funext u
      rw [Finset.sum_comm]
      simp only [matrixExponentialTensorContraction, Finset.mul_sum]]
  exact intervalIntegral.integral_const_mul t _

end FreeProbability.Fock

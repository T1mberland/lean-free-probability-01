import FreeProbability.OperatorValued.MatrixCauchyRightExterior

/-! # Actual matrix Cauchy derivative and Lyapunov identity

The identity is obtained by differentiating actual resolvent Dyson on its open
domain. The covariance continuity bound uses the row operator matrix norm.
No variational spectral-edge formula is asserted.
-/

noncomputable section
open scoped Classical Topology Matrix.Norms.Operator
namespace FreeProbability

variable {I n : Type*} [Fintype I] [Fintype n] [DecidableEq n]

/-- Actual finite matrix covariance as a continuous linear map in row operator norm. -/
def matrixCovarianceContinuous (C : I → Matrix n n ℂ) : Matrix n n ℂ →L[ℂ] Matrix n n ℂ :=
  (matrixCovariance C).mkContinuous (∑ i, ‖C i‖ ^ 2) (matrixCovariance_norm_le C)

@[simp] theorem matrixCovarianceContinuous_apply (C : I → Matrix n n ℂ) (D : Matrix n n ℂ) :
    matrixCovarianceContinuous C D = matrixCovariance C D := rfl

namespace Fock
local instance : PartialOrder (WordSpace I →L[ℂ] WordSpace I) := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing (WordSpace I →L[ℂ] WordSpace I) :=
  CStarAlgebra.spectralOrderedRing _

/-- The actual derivative of the matrix Cauchy transform. -/
def operatorMatrixPencilCauchyDerivative (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ) (z : ℂ) : Matrix n n ℂ :=
  -matrixExpectation (vacuumState I).toProbabilitySpace
    (CStarMatrix.ofMatrix.symm (resolvent (operatorMatrixPencil C₀ C) z) *
      CStarMatrix.ofMatrix.symm (resolvent (operatorMatrixPencil C₀ C) z))

/-- Differentiating the true Dyson equation yields the actual Lyapunov relation. -/
theorem operatorMatrixPencilCauchyDerivative_lyapunov (C₀ : Matrix n n ℂ)
    (C : I → Matrix n n ℂ) (z : ℂ) (hz : z ∈ resolventSet ℂ (operatorMatrixPencil C₀ C)) :
    operatorMatrixPencilCauchyDerivative C₀ C z =
      -(operatorMatrixPencilCauchy C₀ C z * operatorMatrixPencilCauchy C₀ C z) +
        operatorMatrixPencilCauchy C₀ C z *
          matrixCovariance C (operatorMatrixPencilCauchyDerivative C₀ C z) *
            operatorMatrixPencilCauchy C₀ C z := by
  let m := operatorMatrixPencilCauchy C₀ C
  let d := operatorMatrixPencilCauchyDerivative C₀ C z
  have hm : HasDerivAt m d z := operatorMatrixPencilCauchy_hasDerivAt C₀ C z hz
  have hB : HasDerivAt (fun w : ℂ => w • (1 : Matrix n n ℂ) - C₀) 1 z := by
    simpa only [one_smul, sub_zero] using!
      ((hasDerivAt_id z).smul_const (1 : Matrix n n ℂ)).sub (hasDerivAt_const z C₀)
  have hη := (matrixCovarianceContinuous C).hasFDerivAt.comp_hasDerivAt z hm
  have hprod := (hB.sub hη).mul hm
  have hevent : (fun w : ℂ => (w • (1 : Matrix n n ℂ) - C₀ - matrixCovariance C (m w)) * m w) =ᶠ[𝓝 z]
      (fun _ => (1 : Matrix n n ℂ)) := by
    filter_upwards [(spectrum.isOpen_resolventSet (operatorMatrixPencil C₀ C)).mem_nhds hz] with w hw
    exact operatorMatrixPencilCauchy_dyson C₀ C w hw
  have hconst : HasDerivAt (fun _ : ℂ => (1 : Matrix n n ℂ))
      ((1 - matrixCovariance C d) * m z + (z • 1 - C₀ - matrixCovariance C (m z)) * d) z := by
    simpa only [matrixCovarianceContinuous_apply] using! hprod.congr_of_eventuallyEq hevent.symm
  have hzero : HasDerivAt (fun _ : ℂ => (1 : Matrix n n ℂ)) (0 : Matrix n n ℂ) z :=
    hasDerivAt_const z (1 : Matrix n n ℂ)
  have heq : (1 - matrixCovariance C d) * m z +
      (z • 1 - C₀ - matrixCovariance C (m z)) * d = 0 := hconst.unique hzero
  have hleft : m z * (z • (1 : Matrix n n ℂ) - C₀ - matrixCovariance C (m z)) = 1 :=
    mul_eq_one_comm.mp (operatorMatrixPencilCauchy_dyson C₀ C z hz)
  have hstep : m z * m z - m z * matrixCovariance C d * m z + d = 0 := by
    calc
      _ = m z * ((1 - matrixCovariance C d) * m z +
          (z • 1 - C₀ - matrixCovariance C (m z)) * d) := by
        rw [mul_add, ← mul_assoc (m z) (z • 1 - C₀ - matrixCovariance C (m z)) d, hleft]
        noncomm_ring
      _ = 0 := by rw [heq, mul_zero]
  change d = -(m z * m z) + m z * matrixCovariance C d * m z
  calc
    d = -(m z * m z - m z * matrixCovariance C d * m z) :=
      eq_neg_of_add_eq_zero_right hstep
    _ = _ := by abel

end Fock
end FreeProbability

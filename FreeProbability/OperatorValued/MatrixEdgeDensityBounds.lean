import FreeProbability.OperatorValued.MatrixEdgeStateBounds

/-! # Genuine density states and matrix spectral-edge lower bounds -/

noncomputable section
open scoped Classical ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix
namespace FreeProbability
variable {n I : Type*} [Fintype n] [DecidableEq n]

/-- The true trace functional of a density matrix, allowing singular densities. -/
def matrixDensityState (ρ : Matrix n n ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    StarProbabilitySpace (Matrix n n ℂ) where
  expectation :=
    { toFun := fun X => Matrix.trace (ρ * X)
      map_add' := by intros; simp [mul_add]
      map_smul' := by intros; simp }
  map_one := by simpa using htr
  map_star := by
    intro X
    change Matrix.trace (ρ * Xᴴ) = star (Matrix.trace (ρ * X))
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hρ.isHermitian.eq,
      Matrix.trace_mul_comm]
  positive := by
    intro X
    change 0 ≤ Matrix.trace (ρ * (Xᴴ * X))
    have hp : (X * ρ * Xᴴ).PosSemidef := by
      simpa using hρ.conjTranspose_mul_mul_same Xᴴ
    have ht : Matrix.trace (X * ρ * Xᴴ) = Matrix.trace (ρ * (Xᴴ * X)) := by
      rw [Matrix.trace_mul_cycle, Matrix.trace_mul_cycle, mul_assoc]
    rw [← ht]
    exact hp.trace_nonneg

@[simp] theorem matrixDensityState_expectation (ρ : Matrix n n ℂ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) (X : Matrix n n ℂ) :
    (matrixDensityState ρ hρ htr).expectation X = Matrix.trace (ρ * X) := rfl

namespace Fock
variable [Fintype I] [Nonempty n]
/-- Every actual positive semidefinite density of trace one gives this lower
bound for the genuine matrix semicircular spectral edge. -/
theorem operatorMatrixPencilTopEdge_density_lower
    (ρ : Matrix n n ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ)
    (hC₀ : C₀.IsHermitian) (hC : ∀ i, (C i).IsHermitian) :
    (Matrix.trace (ρ * C₀)).re + 2 * Real.sqrt (∑ i, ‖Matrix.trace (ρ * C i)‖ ^ 2) ≤
      operatorMatrixPencilTopEdge C₀ C :=
  operatorMatrixPencilTopEdge_state_lower (matrixDensityState ρ hρ htr) C₀ C hC₀ hC
end Fock
end FreeProbability

import FreeProbability.Fock.FiniteDepthCauchyIdentification

noncomputable section
open scoped Classical Ring
namespace FreeProbability.Examples
variable {I n : Type*} [Fintype I] [Fintype n] [DecidableEq n] [Nonempty n]

-- Scalar drift -3 and vanishing random coefficients permit z=-2 at every depth.
-- Keep the input matrices as named parameters to avoid expanding their norm structures.
example (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ)
    (h₀ : C₀ = ((-3 : ℝ) : ℂ) • 1) (hC : C = fun _ => 0) (L : ℕ) :
    ‖Fock.coefficientMatrixOperator (Fock.operatorMatrixPencilCauchy C₀ C ((-2 : ℝ) : ℂ)) -
        Fock.matrixVacuumCompression (Fock.finiteDepthPencilResolvent C₀ C L (-2))‖ ≤
      2 * ((realSpectralMaximum (Fock.operatorMatrixPencil C₀ C) +
        ‖Fock.operatorMatrixPencil C₀ C‖) / (-2 + ‖Fock.operatorMatrixPencil C₀ C‖)) ^
        (L + 1) / (-2 - realSpectralMaximum (Fock.operatorMatrixPencil C₀ C)) := by
  have hh₀ : C₀.IsHermitian := by
    rw [h₀]
    exact Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint])
  have hhC : ∀ i, (C i).IsHermitian := by
    intro i
    rw [hC]
    exact Matrix.isHermitian_zero
  have hs : Fock.finiteDepthPencilUpperEdge C₀ C = -3 := by
    simpa only [h₀, hC] using
      Fock.finiteDepthPencilUpperEdge_scalar (I := I) (n := n) (-3)
  have hb : realSpectralMaximum (Fock.operatorMatrixPencil C₀ C) = -3 :=
    (Fock.finiteDepthPencilUpperEdge_eq C₀ C).symm.trans hs
  exact Fock.operatorMatrixPencilCauchy_finiteDepth_error C₀ C hh₀ hhC L (-2)
    (by rw [hb]; norm_num)

end FreeProbability.Examples

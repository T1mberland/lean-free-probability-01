import FreeProbability.OperatorValued.MatrixEdgeVariational

/-! # Actual right-exterior matrix Cauchy spectral bounds -/

noncomputable section
open scoped Classical ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix
namespace FreeProbability

private theorem ring_inverse_real_algebraMap {A : Type*} [Ring A] [Algebra ℝ A]
    (r : ℝ) (hr : r ≠ 0) :
    Ring.inverse (algebraMap ℝ A r) = algebraMap ℝ A r⁻¹ := by
  have hu : IsUnit (algebraMap ℝ A r) := (isUnit_iff_ne_zero.mpr hr).map (algebraMap ℝ A)
  have hh := (Ring.inverse_mul_eq_iff_eq_mul (algebraMap ℝ A r) 1
    (algebraMap ℝ A r⁻¹) hu).mpr (by rw [← map_mul, mul_inv_cancel₀ hr, map_one])
  simpa only [mul_one] using hh

/-- A self-adjoint operator bounded above by b has the exact resolvent order
bound throughout x > b, in its genuine C-star order. -/
theorem cstar_resolvent_le_inverse_gap {A : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (a : A) (b x : ℝ)
    (hab : a ≤ algebraMap ℝ A b) (hx : b < x) :
    resolvent a (x : ℂ) ≤ algebraMap ℝ A (x - b)⁻¹ := by
  have hbound : algebraMap ℝ A (x - b) ≤ algebraMap ℂ A (x : ℂ) - a := by
    have hc : algebraMap ℂ A (x : ℂ) = algebraMap ℝ A x :=
      (IsScalarTower.algebraMap_apply ℝ ℂ A x).symm
    rw [map_sub, hc]
    exact sub_le_sub_left hab _
  have h := CStarAlgebra.ringInverse_le_ringInverse hbound
    (isStrictlyPositive_algebraMap (sub_pos.mpr hx))
  rw [ring_inverse_real_algebraMap _ (ne_of_gt (sub_pos.mpr hx))] at h
  exact h

namespace Fock
variable {I n : Type*} [Fintype I] [Fintype n] [DecidableEq n] [Nonempty n]
local instance : PartialOrder (WordSpace I →L[ℂ] WordSpace I) := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing (WordSpace I →L[ℂ] WordSpace I) :=
  CStarAlgebra.spectralOrderedRing _
local instance : Nontrivial (WordSpace I →L[ℂ] WordSpace I) := by
  refine ⟨⟨1, 0, ?_⟩⟩
  intro h
  have hv := congrArg (fun T : WordSpace I →L[ℂ] WordSpace I => ‖T vacuum‖) h
  simp at hv

omit [Nonempty n] in
/-- Actual matrix Cauchy order bound in terms of the genuine spectral-edge gap. -/
theorem operatorMatrixPencilCauchy_le_inverse_edge_gap
    (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ)
    (hC₀ : C₀.IsHermitian) (hC : ∀ i, (C i).IsHermitian)
    (x : ℝ) (hx : operatorMatrixPencilTopEdge C₀ C < x) :
    operatorMatrixPencilCauchy C₀ C x ≤
      (((x - operatorMatrixPencilTopEdge C₀ C)⁻¹ : ℝ) : ℂ) • 1 := by
  have hR := cstar_resolvent_le_inverse_gap (operatorMatrixPencil C₀ C)
    (operatorMatrixPencilTopEdge C₀ C) x
    (le_algebraMap_realSpectralMaximum _ (operatorMatrixPencil_isSelfAdjoint C₀ C hC₀ hC)) hx
  have he := matrixExpectation_posSemidef_of_cstarMatrix_nonneg (vacuumState I)
    ((algebraMap ℝ (CStarMatrix n n (WordSpace I →L[ℂ] WordSpace I))
      (x - operatorMatrixPencilTopEdge C₀ C)⁻¹) -
      resolvent (operatorMatrixPencil C₀ C) (x : ℂ)) (sub_nonneg.mpr hR)
  have hsub (U R : CStarMatrix n n (WordSpace I →L[ℂ] WordSpace I)) :
      CStarMatrix.ofMatrix.symm (U - R) =
      CStarMatrix.ofMatrix.symm U - CStarMatrix.ofMatrix.symm R :=
    by
      apply Matrix.ext
      intro r c
      rfl
  rw [hsub, map_sub] at he
  have hscalar (r : ℝ) : matrixExpectation (vacuumState I).toProbabilitySpace
      (CStarMatrix.ofMatrix.symm (algebraMap ℝ
        (CStarMatrix n n (WordSpace I →L[ℂ] WordSpace I)) r)) = (r : ℂ) • 1 := by
    rw [IsScalarTower.algebraMap_apply ℝ ℂ _ r, Algebra.algebraMap_eq_smul_one]
    change matrixExpectation (vacuumState I).toProbabilitySpace
      ((r : ℂ) • (1 : Matrix n n (WordSpace I →L[ℂ] WordSpace I))) = _
    rw [map_smul]
    congr 1
    simpa using matrixExpectation_scalarMatrixEmbedding (vacuumState I).toProbabilitySpace
      (1 : Matrix n n ℂ)
  rw [hscalar] at he
  have hfinal : operatorMatrixPencilCauchy C₀ C (x : ℂ) ≤
      (((x - operatorMatrixPencilTopEdge C₀ C)⁻¹ : ℝ) : ℂ) • (1 : Matrix n n ℂ) :=
    sub_nonneg.mp he.nonneg
  exact hfinal
/-- Strict positivity and the precise actual edge-gap upper bound hold
simultaneously on the full right exterior. -/
theorem operatorMatrixPencilCauchy_posDef_and_le_inverse_edge_gap
    (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ)
    (hC₀ : C₀.IsHermitian) (hC : ∀ i, (C i).IsHermitian)
    (x : ℝ) (hx : operatorMatrixPencilTopEdge C₀ C < x) :
    (operatorMatrixPencilCauchy C₀ C x).PosDef ∧
      operatorMatrixPencilCauchy C₀ C x ≤
        (((x - operatorMatrixPencilTopEdge C₀ C)⁻¹ : ℝ) : ℂ) • 1 := by
  refine ⟨operatorMatrixPencilCauchy_posDef_right_exterior C₀ C hC₀ hC x ?_,
    operatorMatrixPencilCauchy_le_inverse_edge_gap C₀ C hC₀ hC x hx⟩
  exact (realSpectralMaximum_lt_iff _
    (operatorMatrixPencil_isSelfAdjoint C₀ C hC₀ hC) x).mp hx

/-- The inverse actual Cauchy matrix is bounded below by the true spectral gap. -/
theorem operatorMatrixPencilCauchy_inverse_ge_edge_gap
    (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ)
    (hC₀ : C₀.IsHermitian) (hC : ∀ i, (C i).IsHermitian)
    (x : ℝ) (hx : operatorMatrixPencilTopEdge C₀ C < x) :
    ((x - operatorMatrixPencilTopEdge C₀ C : ℝ) : ℂ) • 1 ≤
      (operatorMatrixPencilCauchy C₀ C x)⁻¹ := by
  obtain ⟨hM, hbound⟩ := operatorMatrixPencilCauchy_posDef_and_le_inverse_edge_gap C₀ C hC₀ hC x hx
  have hscalar (r : ℝ) : (r : ℂ) • (1 : Matrix n n ℂ) = algebraMap ℝ (Matrix n n ℂ) r := by
    rw [Algebra.algebraMap_eq_smul_one, Complex.coe_smul]
  rw [hscalar] at hbound
  have hinv := CStarAlgebra.ringInverse_le_ringInverse hbound
    (hM.isUnit.isStrictlyPositive hM.posSemidef.nonneg)
  rw [ring_inverse_real_algebraMap _ (inv_ne_zero (ne_of_gt (sub_pos.mpr hx))), inv_inv,
    ← Matrix.nonsing_inv_eq_ringInverse, ← hscalar] at hinv
  exact hinv

end Fock
end FreeProbability

import FreeProbability.Fock.FiniteDepthVacuumCompression
import Mathlib.Analysis.CStarAlgebra.Hom
import FreeProbability.OperatorValued.MatrixCauchyRightExterior

/-! # Literal matrix vacuum and spectral compatibility -/
noncomputable section
open scoped Classical Ring ENNReal InnerProductSpace
namespace FreeProbability.Fock
variable {I n : Type*} [Fintype I] [Fintype n] [DecidableEq n]

omit [Fintype I] in
theorem matrixVacuumInclusion_single (j : n) :
    matrixVacuumInclusion (I := I) (lp.single 2 j (1 : ℂ)) =
      lp.single 2 j (vacuum : WordSpace I) := by
  apply lp.ext
  funext k
  simp only [matrixVacuumInclusion_apply, lp.single_apply, Pi.single_apply]
  split_ifs <;> simp

omit [Fintype I] in
theorem matrixVacuumInclusion_adjoint_apply (f : HilbertMatrixSpace n (WordSpace I)) (j : n) :
    (matrixVacuumInclusion (n := n) (I := I)).adjoint f j = inner ℂ vacuum (f j) := by
  have hh := ContinuousLinearMap.adjoint_inner_right
    (matrixVacuumInclusion (n := n) (I := I)) (lp.single 2 j (1 : ℂ)) f
  rw [matrixVacuumInclusion_single, lp.inner_single_left, lp.inner_single_left] at hh
  simpa using hh

/-- The literal scalar matrix acts on the finite coefficient Hilbert space. -/
def coefficientMatrixOperator (D : Matrix n n ℂ) :
    HilbertMatrixSpace n ℂ →L[ℂ] HilbertMatrixSpace n ℂ :=
  hilbertMatrixOperator (fun j k => D j k • (1 : ℂ →L[ℂ] ℂ))

omit [Fintype I] in
/-- Actual Hilbert vacuum compression is exactly the entrywise matrix vacuum expectation. -/
theorem matrixVacuumCompression_hilbertMatrixOperator
    (M : Matrix n n (WordSpace I →L[ℂ] WordSpace I)) :
    matrixVacuumCompression (hilbertMatrixOperator M) =
      coefficientMatrixOperator (matrixExpectation (vacuumState I).toProbabilitySpace M) := by
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext j
  change ((matrixVacuumInclusion (n := n) (I := I)).adjoint
    (hilbertMatrixOperator M (matrixVacuumInclusion v))) j =
      hilbertMatrixOperator (fun j k =>
        matrixExpectation (vacuumState I).toProbabilitySpace M j k •
          (1 : ℂ →L[ℂ] ℂ)) v j
  rw [matrixVacuumInclusion_adjoint_apply]
  have hm := hilbertMatrixOperator_apply M (matrixVacuumInclusion v) j
  have hs := hilbertMatrixOperator_apply (E := ℂ) (fun j k =>
    matrixExpectation (vacuumState I).toProbabilitySpace M j k • (1 : ℂ →L[ℂ] ℂ)) v j
  calc
    _ = inner ℂ vacuum (∑ k, M j k (matrixVacuumInclusion v k)) :=
      congrArg (inner ℂ (vacuum : WordSpace I)) hm
    _ = ∑ k, (matrixExpectation (vacuumState I).toProbabilitySpace M j k •
        (1 : ℂ →L[ℂ] ℂ)) (v k) := by
      rw [inner_sum]
      apply Finset.sum_congr rfl
      intro k _
      change inner ℂ vacuum (M j k (v k • vacuum)) = vacuumExpectation (M j k) * v k
      rw [map_smul, inner_smul_right]
      exact mul_comm _ _
    _ = _ := hs.symm

theorem finiteDepthPencilUpperEdge_eq (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ) :
    finiteDepthPencilUpperEdge C₀ C = realSpectralMaximum (operatorMatrixPencil C₀ C) := by
  unfold finiteDepthPencilUpperEdge realSpectralMaximum
  rw [finiteDepthPencilOperator_eq_representation]
  exact congrArg sSup (AlgEquiv.spectrum_eq
    ((hilbertMatrixStarAlgEquiv (N := n) (E := WordSpace I)).toAlgEquiv.restrictScalars ℝ) _)

theorem finiteDepthPencilOperator_norm_eq (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ) :
    ‖finiteDepthPencilOperator C₀ C‖ = ‖operatorMatrixPencil C₀ C‖ := by
  rw [finiteDepthPencilOperator_eq_representation]
  exact NonUnitalStarAlgHom.norm_map
    (hilbertMatrixStarAlgEquiv (N := n) (E := WordSpace I))
    (hilbertMatrixStarAlgEquiv (N := n) (E := WordSpace I)).injective _

/-- The actual pencil resolvent is carried to its literal Hilbert block resolvent. -/
theorem finiteDepthPencilOperator_resolvent (C₀ : Matrix n n ℂ)
    (C : I → Matrix n n ℂ) (z : ℂ) (hz : z ∈ resolventSet ℂ (operatorMatrixPencil C₀ C)) :
    (hilbertMatrixStarAlgEquiv (N := n) (E := WordSpace I))
      (resolvent (operatorMatrixPencil C₀ C) z) =
        (z • 1 - finiteDepthPencilOperator C₀ C)⁻¹ʳ := by
  let f := hilbertMatrixStarAlgEquiv (N := n) (E := WordSpace I)
  let a := algebraMap ℂ _ z - operatorMatrixPencil C₀ C
  have hu : IsUnit a := hz
  have hf : IsUnit (f a) := hu.map f.toAlgEquiv.toMonoidHom
  have hh := (Ring.inverse_mul_eq_iff_eq_mul (f a) 1 (f a⁻¹ʳ) hf).mpr (by
    rw [← map_mul, Ring.mul_inverse_cancel a hu, map_one])
  have he : f a = z • 1 - finiteDepthPencilOperator C₀ C := by
    simp only [a, map_sub, Algebra.algebraMap_eq_smul_one, map_smul, map_one]
    rfl
  rw [he] at hh
  simpa only [mul_one, resolvent, a, f] using hh.symm

/-- The matrix Cauchy transform acts exactly as the genuine compressed resolvent. -/
theorem coefficientMatrixOperator_pencilCauchy (C₀ : Matrix n n ℂ)
    (C : I → Matrix n n ℂ) (z : ℂ) (hz : z ∈ resolventSet ℂ (operatorMatrixPencil C₀ C)) :
    coefficientMatrixOperator (operatorMatrixPencilCauchy C₀ C z) =
      matrixVacuumCompression ((z • 1 - finiteDepthPencilOperator C₀ C)⁻¹ʳ) := by
  rw [← finiteDepthPencilOperator_resolvent C₀ C z hz]
  exact (matrixVacuumCompression_hilbertMatrixOperator
    (CStarMatrix.ofMatrix.symm (resolvent (operatorMatrixPencil C₀ C) z))).symm

variable [Nonempty n]

/-- The existing matrix Cauchy transform satisfies the full operator-norm finite-depth bound. -/
theorem operatorMatrixPencilCauchy_finiteDepth_error (C₀ : Matrix n n ℂ)
    (C : I → Matrix n n ℂ) (hC₀ : C₀.IsHermitian) (hC : ∀ i, (C i).IsHermitian)
    (L : ℕ) (z : ℝ) (hz : realSpectralMaximum (operatorMatrixPencil C₀ C) < z) :
    ‖coefficientMatrixOperator (operatorMatrixPencilCauchy C₀ C z) -
        matrixVacuumCompression (finiteDepthPencilResolvent C₀ C L z)‖ ≤
      2 * ((realSpectralMaximum (operatorMatrixPencil C₀ C) + ‖operatorMatrixPencil C₀ C‖) /
        (z + ‖operatorMatrixPencil C₀ C‖)) ^ (L + 1) /
        (z - realSpectralMaximum (operatorMatrixPencil C₀ C)) := by
  have hr := cstar_mem_resolventSet_of_real_spectrum_lt (operatorMatrixPencil C₀ C) z
    (fun t ht => (le_realSpectralMaximum _ t ht).trans_lt hz)
  rw [coefficientMatrixOperator_pencilCauchy C₀ C z hr]
  have hh := finiteDepthPencilVacuumCompression_error C₀ C hC₀ hC L z
    (by simpa only [finiteDepthPencilUpperEdge_eq] using hz)
  simpa only [finiteDepthPencilUpperEdge_eq, finiteDepthPencilOperator_norm_eq] using hh

end FreeProbability.Fock

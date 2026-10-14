import FreeProbability.OperatorValued.MatrixResolventExterior
import FreeProbability.OperatorValued.MatrixPositiveExpectation
import Mathlib.Analysis.Matrix.Order

/-! # Positive actual matrix Cauchy transform on the full real right exterior

The domain is exactly that every real spectral value is strictly smaller than
the argument, rather than only the sufficient operator-norm bound.
-/

noncomputable section
open scoped Classical ComplexOrder MatrixOrder
open Matrix
namespace FreeProbability

/-- The full real right exterior lies in the genuine complex resolvent domain. -/
theorem cstar_mem_resolventSet_of_real_spectrum_lt {A : Type*} [CStarAlgebra A]
    (a : A) (x : ℝ) (hx : ∀ t ∈ spectrum ℝ a, t < x) :
    (x : ℂ) ∈ resolventSet ℂ a := by
  have hr : x ∈ resolventSet ℝ a := by
    by_contra h
    exact (lt_irrefl x) (hx x h)
  change IsUnit (algebraMap ℂ A (x : ℂ) - a)
  have hc : algebraMap ℂ A (x : ℂ) = algebraMap ℝ A x :=
    (IsScalarTower.algebraMap_apply ℝ ℂ A x).symm
  rw [hc]
  exact hr

/-- The true inverse is positive throughout the exact right spectral exterior
of a self-adjoint element in a nontrivial C-star algebra. -/
theorem cstar_resolvent_nonneg_of_real_spectrum_lt {A : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
    (a : A) (ha : IsSelfAdjoint a) (x : ℝ) (hx : ∀ t ∈ spectrum ℝ a, t < x) :
    0 ≤ resolvent a (x : ℂ) := by
  have hbound : a ≤ algebraMap ℝ A x := le_algebraMap_of_spectrum_le
    (fun t ht => (hx t ht).le) ha
  have hp : 0 ≤ algebraMap ℂ A (x : ℂ) - a := by
    have hc : algebraMap ℂ A (x : ℂ) = algebraMap ℝ A x :=
      (IsScalarTower.algebraMap_apply ℝ ℂ A x).symm
    rw [hc]
    exact sub_nonneg.mpr hbound
  have hr := cstar_mem_resolventSet_of_real_spectrum_lt a x hx
  obtain ⟨u, hu⟩ := hr
  change 0 ≤ Ring.inverse (algebraMap ℂ A (x : ℂ) - a)
  rw [← hu, Ring.inverse_unit]
  exact CFC.inv_nonneg_of_nonneg u (by rw [hu]; exact hp)

namespace Fock
variable {I n : Type*} [Fintype I] [Fintype n] [DecidableEq n]
local instance : PartialOrder (WordSpace I →L[ℂ] WordSpace I) := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing (WordSpace I →L[ℂ] WordSpace I) :=
  CStarAlgebra.spectralOrderedRing _

/-- Exact right-exterior Dyson for the actual matrix pencil. -/
theorem operatorMatrixPencilCauchy_inverse_dyson_right_exterior (C₀ : Matrix n n ℂ)
    (C : I → Matrix n n ℂ) (x : ℝ)
    (hx : ∀ t ∈ spectrum ℝ (operatorMatrixPencil C₀ C), t < x) :
    (operatorMatrixPencilCauchy C₀ C x)⁻¹ = (x : ℂ) • (1 : Matrix n n ℂ) - C₀ -
      matrixCovariance C (operatorMatrixPencilCauchy C₀ C x) :=
  operatorMatrixPencilCauchy_inverse_dyson C₀ C x
    (cstar_mem_resolventSet_of_real_spectrum_lt _ x hx)

/-- The actual matrix Cauchy transform is strictly positive on the FULL real
right spectral exterior of a Hermitian pencil, including empty dimensions. -/
theorem operatorMatrixPencilCauchy_posDef_right_exterior (C₀ : Matrix n n ℂ)
    (C : I → Matrix n n ℂ) (hC₀ : C₀.IsHermitian) (hC : ∀ i, (C i).IsHermitian)
    (x : ℝ) (hx : ∀ t ∈ spectrum ℝ (operatorMatrixPencil C₀ C), t < x) :
    (operatorMatrixPencilCauchy C₀ C x).PosDef := by
  by_cases hn : Nonempty n
  · have := hn
    have : Nontrivial (WordSpace I →L[ℂ] WordSpace I) := by
      refine ⟨⟨1, 0, ?_⟩⟩
      intro h
      have hv := congrArg (fun T : WordSpace I →L[ℂ] WordSpace I => ‖T vacuum‖) h
      simp at hv
    have hp := cstar_resolvent_nonneg_of_real_spectrum_lt (operatorMatrixPencil C₀ C)
      (operatorMatrixPencil_isSelfAdjoint C₀ C hC₀ hC) x hx
    have hm : (operatorMatrixPencilCauchy C₀ C x).PosSemidef :=
      matrixExpectation_posSemidef_of_cstarMatrix_nonneg (vacuumState I) _ hp
    apply hm.posDef_iff_isUnit.mpr
    have hr := cstar_mem_resolventSet_of_real_spectrum_lt (operatorMatrixPencil C₀ C) x hx
    have he := operatorMatrixPencilCauchy_dyson C₀ C x hr
    apply (Matrix.isUnit_iff_isUnit_det (operatorMatrixPencilCauchy C₀ C x)).mpr
    apply isUnit_of_mul_isUnit_right (x :=
      ((x : ℂ) • (1 : Matrix n n ℂ) - C₀ - matrixCovariance C (operatorMatrixPencilCauchy C₀ C x)).det)
    rw [← Matrix.det_mul, he, Matrix.det_one]
    exact isUnit_one
  · have : IsEmpty n := not_nonempty_iff.mp hn
    apply PosDef.of_dotProduct_mulVec_pos
    · apply IsHermitian.ext
      intro r _
      exact isEmptyElim r
    · intro v hv
      exact False.elim (hv (funext (fun r => isEmptyElim r)))

end Fock
end FreeProbability

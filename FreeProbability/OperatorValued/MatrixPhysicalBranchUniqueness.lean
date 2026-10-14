import FreeProbability.OperatorValued.MatrixDysonAnalyticUniqueness
import Mathlib.Analysis.Complex.Convex

/-! # The actual normalized analytic matrix Dyson branch in the upper half-plane

The competing branch is analytic, solves the actual covariance Dyson equation,
and is normalized at infinity WITHIN the upper half-plane. The actual Fock
Cauchy transform supplies these properties by earlier verified theorems.
This does not assert uniqueness of arbitrary pointwise negative-imaginary matrices.
-/

noncomputable section
open scoped Classical Topology Matrix.Norms.Operator
namespace FreeProbability.Fock

variable {I n : Type*} [Fintype I] [Fintype n] [DecidableEq n]
local instance : PartialOrder (WordSpace I →L[ℂ] WordSpace I) := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing (WordSpace I →L[ℂ] WordSpace I) :=
  CStarAlgebra.spectralOrderedRing _

private theorem upperHalfPlane_unbounded : ¬ Bornology.IsBounded {z : ℂ | 0 < z.im} := by
  intro h
  obtain ⟨R, hR⟩ := h.exists_norm_le
  let t : ℝ := max R 0 + 1
  have ht : 0 < t := by dsimp [t]; positivity
  have hm := hR ((t : ℂ) * Complex.I) (by simp [ht])
  simp only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
    abs_of_pos ht] at hm
  have hmax := le_max_left R 0
  dsimp [t] at hm
  linarith

/-- Every normalized analytic solution of the affine covariance Dyson equation
in the upper half-plane is the actual Fock matrix Cauchy transform. -/
theorem operatorMatrixPencilCauchy_unique_normalized_analytic
    (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ) (hC₀ : C₀.IsHermitian)
    (hC : ∀ i, (C i).IsHermitian) (F : ℂ → Matrix n n ℂ)
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.im})
    (hFD : ∀ z : ℂ, 0 < z.im →
      (z • (1 : Matrix n n ℂ) - C₀ - matrixCovariance C (F z)) * F z = 1)
    (hFone : Filter.Tendsto (fun z : ℂ => z • F z)
      (Bornology.cobounded ℂ ⊓ Filter.principal {z : ℂ | 0 < z.im})
      (𝓝 (1 : Matrix n n ℂ))) :
    Set.EqOn F (operatorMatrixPencilCauchy C₀ C) {z : ℂ | 0 < z.im} := by
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hconn : IsPreconnected {z : ℂ | 0 < z.im} := (convex_halfSpace_im_gt (0 : ℝ)).isPreconnected
  have hdomain (z : ℂ) (hz : 0 < z.im) : z ∈ resolventSet ℂ (operatorMatrixPencil C₀ C) :=
    StarProbabilitySpace.selfAdjoint_mem_resolventSet_of_im_ne_zero (operatorMatrixPencil C₀ C)
      (operatorMatrixPencil_isSelfAdjoint C₀ C hC₀ hC) z hz.ne'
  have hG : AnalyticOnNhd ℂ (operatorMatrixPencilCauchy C₀ C) {z : ℂ | 0 < z.im} := by
    apply DifferentiableOn.analyticOnNhd _ hopen
    intro z hz
    have hd := (operatorMatrixPencilCauchy_hasDerivAt C₀ C z (hdomain z hz)).differentiableAt
    exact hd.differentiableWithinAt
  have hGone : Filter.Tendsto (fun z : ℂ => z • operatorMatrixPencilCauchy C₀ C z)
      (Bornology.cobounded ℂ ⊓ Filter.principal {z : ℂ | 0 < z.im})
      (𝓝 (1 : Matrix n n ℂ)) := by
    simpa using! (operatorMatrixPencilCauchy_smul_tendsto_one C₀ C).mono_left inf_le_left
  exact matrixDyson_analytic_unique_of_normalized C
    (fun z => z • (1 : Matrix n n ℂ) - C₀) F (operatorMatrixPencilCauchy C₀ C)
    {z : ℂ | 0 < z.im} hopen hconn upperHalfPlane_unbounded hF hG
    (fun z hz => hFD z hz)
    (fun z hz => operatorMatrixPencilCauchy_dyson C₀ C z (hdomain z hz)) hFone hGone

end FreeProbability.Fock

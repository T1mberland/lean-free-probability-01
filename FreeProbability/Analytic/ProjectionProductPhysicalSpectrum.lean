import FreeProbability.Analytic.ProjectionProductPhysicalLimitsTwo
import FreeProbability.Analytic.SpectralMeasureCauchy

/-! # Faithful ambient spectrum and actual operator Cauchy identification -/

noncomputable section
open MeasureTheory
namespace FreeProbability
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
namespace StarProbabilitySpace
variable (φ : FreeProbability.StarProbabilitySpace A)

/-- With faithfulness, the law edge is also the greatest point of the ACTUAL
ambient operator spectrum. -/
theorem iteratedHalfProjection_spectrum_isGreatest
    (hφ : IsTracial φ.toProbabilitySpace) (hfaith : IsFaithful φ.toProbabilitySpace)
    (L : ℕ) (hL : 2 ≤ L) {B : Fin L → Subalgebra ℂ A}
    (hf : FreelyIndependent φ.toProbabilitySpace B) (p : Fin L → A)
    (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, IsStarProjection (p i))
    (hE : ∀ i, φ.expectation (p i) = (1 / 2 : ℂ)) :
    IsGreatest (spectrum ℝ (iteratedPositiveProduct L p)) (halfProjectionRightEdge L) := by
  have ha := (iteratedPositiveProduct_nonneg L p (fun i => (hp i).nonneg)).isSelfAdjoint
  rw [← spectralMeasure_support_eq_spectrum φ ha hfaith]
  exact φ.iteratedHalfProjection_law_support_isGreatest hφ L hL hf p hpB hp hE

/-- Faithfulness supplies the FULL actual operator resolvent domain above the
law edge. Without it, law exterior alone need not exclude ambient spectrum. -/
theorem iteratedHalfProjection_mem_resolventSet_of_gt_edge
    (hφ : IsTracial φ.toProbabilitySpace) (hfaith : IsFaithful φ.toProbabilitySpace)
    (L : ℕ) (hL : 2 ≤ L) {B : Fin L → Subalgebra ℂ A}
    (hf : FreelyIndependent φ.toProbabilitySpace B) (p : Fin L → A)
    (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, IsStarProjection (p i))
    (hE : ∀ i, φ.expectation (p i) = (1 / 2 : ℂ)) (x : ℝ)
    (hx : halfProjectionRightEdge L < x) :
    (x : ℂ) ∈ resolventSet ℂ (iteratedPositiveProduct L p) := by
  have hbound := (φ.iteratedHalfProjection_spectrum_isGreatest hφ hfaith L hL hf p hpB hp hE).2
  have hr : x ∈ resolventSet ℝ (iteratedPositiveProduct L p) := by
    by_contra hn
    exact (not_lt_of_ge (hbound hn)) hx
  change IsUnit (algebraMap ℂ A (x : ℂ) - iteratedPositiveProduct L p)
  have hc : algebraMap ℂ A (x : ℂ) = algebraMap ℝ A x :=
    (IsScalarTower.algebraMap_apply ℝ ℂ A x).symm
  rw [hc]
  exact hr

/-- On the ACTUAL operator resolvent set, its genuine Cauchy transform equals
the real probability-law Cauchy integral; faithfulness is unnecessary here. -/
theorem iteratedProjection_operatorCauchyTransform_eq_realLawCauchy
    (L : ℕ) (p : Fin L → A) (hp : ∀ i, IsStarProjection (p i)) (x : ℝ)
    (hx : (x : ℂ) ∈ resolventSet ℂ (iteratedPositiveProduct L p)) :
    φ.cauchyTransform (iteratedPositiveProduct L p) (x : ℂ) =
      (realProbabilityCauchyTransform
        (iteratedPositiveProbabilityLaw φ L p (fun i => (hp i).nonneg)) x : ℂ) := by
  have ha := (iteratedPositiveProduct_nonneg L p (fun i => (hp i).nonneg)).isSelfAdjoint
  rw [cauchyTransform_eq_spectralIntegral φ ha (x : ℂ) hx]
  change (∫ y : ℝ, ((x : ℂ) - (y : ℂ))⁻¹ ∂spectralMeasure φ ha) =
    (((∫ y : ℝ, (x - y)⁻¹ ∂spectralMeasure φ ha) : ℝ) : ℂ)
  simp_rw [← Complex.ofReal_sub, ← Complex.ofReal_inv]
  exact integral_complex_ofReal

/-- With a faithful state, the operator and law Cauchy transforms agree on
EVERY point of the sharp right exterior. -/
theorem iteratedHalfProjection_operatorCauchyTransform_eq_realLawCauchy
    (hφ : IsTracial φ.toProbabilitySpace) (hfaith : IsFaithful φ.toProbabilitySpace)
    (L : ℕ) (hL : 2 ≤ L) {B : Fin L → Subalgebra ℂ A}
    (hf : FreelyIndependent φ.toProbabilitySpace B) (p : Fin L → A)
    (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, IsStarProjection (p i))
    (hE : ∀ i, φ.expectation (p i) = (1 / 2 : ℂ)) (x : ℝ)
    (hx : halfProjectionRightEdge L < x) :
    φ.cauchyTransform (iteratedPositiveProduct L p) (x : ℂ) =
      (realProbabilityCauchyTransform
        (iteratedPositiveProbabilityLaw φ L p (fun i => (hp i).nonneg)) x : ℂ) :=
  φ.iteratedProjection_operatorCauchyTransform_eq_realLawCauchy L p hp x
    (φ.iteratedHalfProjection_mem_resolventSet_of_gt_edge hφ hfaith L hL hf p hpB hp hE x hx)
/-- The actual operator Cauchy parameter is precisely the verified physical
law parameter on the full faithful exterior. -/
theorem iteratedHalfProjection_operatorCauchy_physical_parameter
    (hφ : IsTracial φ.toProbabilitySpace) (hfaith : IsFaithful φ.toProbabilitySpace)
    (L : ℕ) (hL : 2 ≤ L) {B : Fin L → Subalgebra ℂ A}
    (hf : FreelyIndependent φ.toProbabilitySpace B) (p : Fin L → A)
    (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, IsStarProjection (p i))
    (hE : ∀ i, φ.expectation (p i) = (1 / 2 : ℂ)) (x : ℝ)
    (hx : halfProjectionRightEdge L < x) :
    (x : ℂ) * φ.cauchyTransform (iteratedPositiveProduct L p) (x : ℂ) - 1 =
      (φ.halfProjectionExteriorW L p hp x : ℂ) := by
  rw [φ.iteratedHalfProjection_operatorCauchyTransform_eq_realLawCauchy
    hφ hfaith L hL hf p hpB hp hE x hx]
  simp only [halfProjectionExteriorW, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_one]

/-- The faithful ambient spectral right edge is exactly the sharp law edge. -/
theorem iteratedHalfProjection_spectral_right_edge
    (hφ : IsTracial φ.toProbabilitySpace) (hfaith : IsFaithful φ.toProbabilitySpace)
    (L : ℕ) (hL : 2 ≤ L) {B : Fin L → Subalgebra ℂ A}
    (hf : FreelyIndependent φ.toProbabilitySpace B) (p : Fin L → A)
    (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, IsStarProjection (p i))
    (hE : ∀ i, φ.expectation (p i) = (1 / 2 : ℂ)) :
    sSup (spectrum ℝ (iteratedPositiveProduct L p)) = halfProjectionRightEdge L :=
  (φ.iteratedHalfProjection_spectrum_isGreatest hφ hfaith L hL hf p hpB hp hE).csSup_eq
end StarProbabilitySpace
end FreeProbability

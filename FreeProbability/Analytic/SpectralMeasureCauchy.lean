import FreeProbability.Analytic.SpectralMeasureCalculus
import FreeProbability.Analytic.Transform

/-!
# Actual spectral Cauchy integral representation on the whole resolvent set

The kernel need only be continuous on the actual spectrum. Real exterior
resolvent points are included, despite the kernel's pole elsewhere on the line.
-/

noncomputable section
open MeasureTheory

namespace FreeProbability

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (φ : StarProbabilitySpace A) {a : A} (ha : IsSelfAdjoint a)

omit [PartialOrder A] [StarOrderedRing A] φ in
/-- The actual resolvent is the actual complex continuous-functional-calculus inverse kernel. -/
theorem resolvent_eq_cfc_inverse_kernel (ha : IsSelfAdjoint a) (z : ℂ) (hz : z ∈ resolventSet ℂ a) :
    resolvent a z = cfc (fun x : ℂ => (z - x)⁻¹) a := by
  have hne : ∀ x ∈ spectrum ℂ a, z - x ≠ 0 := by
    intro x hx he
    have heq := sub_eq_zero.mp he
    subst x
    exact (spectrum.notMem_iff.mpr hz) hx
  have hsub : cfc (fun x : ℂ => z - x) a = algebraMap ℂ A z - a := by
    have hs := cfc_sub (fun _ : ℂ => z) id a
    rw [cfc_const z a ha.isStarNormal, cfc_id ℂ a ha.isStarNormal] at hs
    exact hs
  rw [cfc_inv _ a hne (continuous_const.sub continuous_id).continuousOn ha.isStarNormal, hsub]
  rfl

/-- The genuine Cauchy transform is the integral of the resolvent kernel on the entire resolvent set. -/
theorem cauchyTransform_eq_spectralIntegral (z : ℂ) (hz : z ∈ resolventSet ℂ a) :
    φ.cauchyTransform a z = ∫ x : ℝ, (z - (x : ℂ))⁻¹ ∂spectralMeasure φ ha := by
  have hne : ∀ x ∈ spectrum ℂ a, z - x ≠ 0 := by
    intro x hx he
    have heq := sub_eq_zero.mp he
    subst x
    exact (spectrum.notMem_iff.mpr hz) hx
  have hc : ContinuousOn (fun x : ℂ => (z - x)⁻¹) (spectrum ℂ a) :=
    (continuous_const.sub continuous_id).continuousOn.inv₀ hne
  rw [StarProbabilitySpace.cauchyTransform, resolvent_eq_cfc_inverse_kernel ha z hz]
  exact expectation_complex_cfc_eq_integral φ ha _ hc

end FreeProbability

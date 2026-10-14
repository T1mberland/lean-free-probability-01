import FreeProbability.Analytic.SpectralMeasureConvergence
import FreeProbability.Analytic.SpectralMeasureCauchy
import FreeProbability.Analytic.CauchyHalfPlane

/-!
# Bounded moment convergence gives every nonreal Cauchy-transform limit

This uses actual spectral probability integrals and polynomial approximation on
common compact spectra. It has no exterior-series restriction on `‖z‖`.
-/

noncomputable section
open scoped Classical Topology
open MeasureTheory

namespace FreeProbability

variable {ι A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {B : ι → Type*} [∀ i, CStarAlgebra (B i)] [∀ i, PartialOrder (B i)] [∀ i, StarOrderedRing (B i)]
  (φ : StarProbabilitySpace A) (ψ : ∀ i, StarProbabilitySpace (B i))

/-- Convergence extends to every complex continuous test function on the real line. -/
theorem tendsto_complex_spectralIntegral_of_bounded_power_moments (a : A) (ha : IsSelfAdjoint a)
    (b : ∀ i, B i) (hb : ∀ i, IsSelfAdjoint (b i)) (l : Filter ι)
    (hm : ∀ n : ℕ, Filter.Tendsto (fun i => (ψ i).expectation (b i ^ n)) l (𝓝 (φ.expectation (a ^ n))))
    (R : ℝ) (hbound : ∀ᶠ i in l, ‖b i‖ ≤ R) (f : C(ℝ, ℂ)) :
    Filter.Tendsto (fun i => ∫ x, f x ∂spectralMeasure (ψ i) (hb i)) l
      (𝓝 (∫ x, f x ∂spectralMeasure φ ha)) := by
  let fr : C(ℝ, ℝ) := ⟨fun x => (f x).re, Complex.continuous_re.comp f.continuous⟩
  let fi : C(ℝ, ℝ) := ⟨fun x => (f x).im, Complex.continuous_im.comp f.continuous⟩
  have hr := tendsto_spectralIntegral_of_bounded_power_moments φ ψ a ha b hb l hm R hbound fr
  have hi := tendsto_spectralIntegral_of_bounded_power_moments φ ψ a ha b hb l hm R hbound fi
  have hc := ((Complex.continuous_ofReal.tendsto _).comp hr).add
    (((Complex.continuous_ofReal.tendsto _).comp hi).mul_const Complex.I)
  have he (i : ι) : (∫ x, fr x ∂spectralMeasure (ψ i) (hb i) : ℝ) +
      (∫ x, fi x ∂spectralMeasure (ψ i) (hb i) : ℝ) * Complex.I =
        ∫ x, f x ∂spectralMeasure (ψ i) (hb i) := by
    have ht := integral_re_add_im (integrable_spectralMeasure (ψ i) (hb i) f f.continuous.continuousOn)
    simp only [RCLike.re_to_complex, RCLike.im_to_complex, RCLike.I_to_complex] at ht
    convert ht using 1
  have hea : (∫ x, fr x ∂spectralMeasure φ ha : ℝ) +
      (∫ x, fi x ∂spectralMeasure φ ha : ℝ) * Complex.I = ∫ x, f x ∂spectralMeasure φ ha := by
    have ht := integral_re_add_im (integrable_spectralMeasure φ ha f f.continuous.continuousOn)
    simp only [RCLike.re_to_complex, RCLike.im_to_complex, RCLike.I_to_complex] at ht
    convert ht using 1
  rw [hea] at hc
  exact hc.congr (fun i => he i)

/-- Actual Cauchy transforms converge at every nonreal point under bounded moment convergence. -/
theorem tendsto_cauchyTransform_all_nonreal_of_bounded_power_moments (a : A) (ha : IsSelfAdjoint a)
    (b : ∀ i, B i) (hb : ∀ i, IsSelfAdjoint (b i)) (l : Filter ι)
    (hm : ∀ n : ℕ, Filter.Tendsto (fun i => (ψ i).expectation (b i ^ n)) l (𝓝 (φ.expectation (a ^ n))))
    (R : ℝ) (hbound : ∀ᶠ i in l, ‖b i‖ ≤ R) (z : ℂ) (hz : z.im ≠ 0) :
    Filter.Tendsto (fun i => (ψ i).cauchyTransform (b i) z) l (𝓝 (φ.cauchyTransform a z)) := by
  have hne (x : ℝ) : z - (x : ℂ) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im (sub_eq_zero.mp h)
    exact hz (by simpa using hi)
  let f : C(ℝ, ℂ) := ⟨fun x => (z - (x : ℂ))⁻¹,
    (continuous_const.sub Complex.continuous_ofReal).inv₀ hne⟩
  have ht := tendsto_complex_spectralIntegral_of_bounded_power_moments φ ψ a ha b hb l hm R hbound f
  have he i := cauchyTransform_eq_spectralIntegral (ψ i) (hb i) z
    (StarProbabilitySpace.selfAdjoint_mem_resolventSet_of_im_ne_zero (b i) (hb i) z hz)
  have hea := cauchyTransform_eq_spectralIntegral φ ha z
    (StarProbabilitySpace.selfAdjoint_mem_resolventSet_of_im_ne_zero a ha z hz)
  simp only [f, ContinuousMap.coe_mk] at ht
  simpa only [← he, ← hea] using ht

end FreeProbability

import FreeProbability.Analytic.Transform
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Complex.CauchyIntegral

/-! # Cauchy transforms on the resolvent set and upper half-plane

Selfadjoint spectra are real. The resolvent identity and positivity of a
normalized state give strict imaginary-part negativity and the half-plane
norm bound; faithfulness of the state is unnecessary.
-/

namespace FreeProbability.StarProbabilitySpace
open scoped ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (φ : FreeProbability.StarProbabilitySpace A)

omit [PartialOrder A] [StarOrderedRing A] φ in
theorem selfAdjoint_mem_resolventSet_of_im_ne_zero (a : A) (ha : IsSelfAdjoint a)
    (z : ℂ) (hz : z.im ≠ 0) : z ∈ resolventSet ℂ a := by
  by_contra hn
  exact hz (ha.im_eq_zero_of_mem_spectrum hn)

omit [PartialOrder A] [StarOrderedRing A] φ in
theorem inverse_sub_star_inverse (x : A) (hx : IsUnit x) :
    Ring.inverse x - star (Ring.inverse x) =
      Ring.inverse x * (star x - x) * star (Ring.inverse x) := by
  have hr := Ring.inverse_mul_cancel x hx
  have hs : star x * star (Ring.inverse x) = 1 := by
    simpa only [star_mul, star_one] using congrArg star hr
  symm
  rw [mul_sub, sub_mul, mul_assoc (Ring.inverse x) (star x), hs,
    mul_one, hr, one_mul]

omit [PartialOrder A] [StarOrderedRing A] in
theorem cauchyTransform_sub_star (a : A) (ha : IsSelfAdjoint a)
    (z : ℂ) (hz : z ∈ resolventSet ℂ a) :
    φ.cauchyTransform a z - star (φ.cauchyTransform a z) =
      (star z - z) * φ.expectation (resolvent a z * star (resolvent a z)) := by
  have he : star (algebraMap ℂ A z - a) - (algebraMap ℂ A z - a) = (star z - z) • (1 : A) := by
    simp only [Algebra.algebraMap_eq_smul_one, star_sub, star_smul, star_one, ha.star_eq,
      sub_smul]
    abel
  have hr := inverse_sub_star_inverse (algebraMap ℂ A z - a) hz
  rw [he] at hr
  simp only [mul_smul_comm, mul_one, smul_mul_assoc] at hr
  have h := congrArg φ.expectation hr
  simpa only [map_sub, φ.map_star, map_smul, smul_eq_mul, cauchyTransform, resolvent] using h

omit [PartialOrder A] [StarOrderedRing A] in
theorem cauchyTransform_im (a : A) (ha : IsSelfAdjoint a)
    (z : ℂ) (hz : z ∈ resolventSet ℂ a) :
    (φ.cauchyTransform a z).im =
      -z.im * (φ.expectation (resolvent a z * star (resolvent a z))).re := by
  have h := congrArg Complex.im (φ.cauchyTransform_sub_star a ha z hz)
  simp only [Complex.sub_im, Complex.star_def, Complex.conj_im, Complex.mul_im,
    Complex.sub_re, Complex.conj_re, sub_self, zero_mul] at h
  linarith

theorem expectation_inverse_mul_star_re_pos (x : A) (hx : IsUnit x) :
    0 < (φ.expectation (Ring.inverse x * star (Ring.inverse x))).re := by
  have hp : 0 ≤ φ.expectation (Ring.inverse x * star (Ring.inverse x)) := by
    simpa only [star_star] using φ.positive (star (Ring.inverse x))
  have hn : ‖φ.expectation (Ring.inverse x * star (Ring.inverse x))‖ =
      (φ.expectation (Ring.inverse x * star (Ring.inverse x))).re := by
    simpa only [Complex.ofReal_re] using congrArg Complex.re (Complex.eq_coe_norm_of_nonneg hp).symm
  have hs := φ.expectation_star_mul_norm_sq_le (star (Ring.inverse x)) x
  rw [star_star, Ring.inverse_mul_cancel x hx, φ.map_one, norm_one, one_pow, hn] at hs
  have hq := norm_nonneg (φ.expectation (star x * x))
  nlinarith

theorem cauchyTransform_im_neg (a : A) (ha : IsSelfAdjoint a)
    (z : ℂ) (hz : 0 < z.im) : (φ.cauchyTransform a z).im < 0 := by
  have hr := selfAdjoint_mem_resolventSet_of_im_ne_zero a ha z hz.ne'
  rw [φ.cauchyTransform_im a ha z hr]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos hz)
    (φ.expectation_inverse_mul_star_re_pos (algebraMap ℂ A z - a) hr)


/-- The upper-half-plane bound holds for every positive normalized state,
including nonfaithful states. -/
theorem cauchyTransform_norm_le_inv_im (a : A) (ha : IsSelfAdjoint a)
    (z : ℂ) (hz : 0 < z.im) : ‖φ.cauchyTransform a z‖ ≤ 1 / z.im := by
  have hr := selfAdjoint_mem_resolventSet_of_im_ne_zero a ha z hz.ne'
  have hp : 0 ≤ φ.expectation (resolvent a z * star (resolvent a z)) := by
    simpa only [star_star] using φ.positive (star (resolvent a z))
  have hn : ‖φ.expectation (resolvent a z * star (resolvent a z))‖ =
      (φ.expectation (resolvent a z * star (resolvent a z))).re := by
    simpa only [Complex.ofReal_re] using congrArg Complex.re (Complex.eq_coe_norm_of_nonneg hp).symm
  have hs : ‖φ.cauchyTransform a z‖ ^ 2 ≤
      (φ.expectation (resolvent a z * star (resolvent a z))).re := by
    have h := φ.expectation_norm_sq_le (star (resolvent a z))
    simpa only [φ.map_star, norm_star, star_star, cauchyTransform, hn] using h
  have hi : -(φ.cauchyTransform a z).im ≤ ‖φ.cauchyTransform a z‖ :=
    (neg_le_abs _).trans (Complex.abs_im_le_norm _)
  have hb : z.im * ‖φ.cauchyTransform a z‖ ^ 2 ≤ ‖φ.cauchyTransform a z‖ := by
    calc
      _ ≤ z.im * (φ.expectation (resolvent a z * star (resolvent a z))).re :=
        mul_le_mul_of_nonneg_left hs hz.le
      _ = -(φ.cauchyTransform a z).im := by rw [φ.cauchyTransform_im a ha z hr]; ring
      _ ≤ _ := hi
  apply (le_div_iff₀ hz).mpr
  by_cases hzero : ‖φ.cauchyTransform a z‖ = 0
  · simp only [hzero, zero_mul, zero_le_one]
  · have hpos : 0 < ‖φ.cauchyTransform a z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    apply (mul_le_mul_iff_right₀ hpos).mp
    nlinarith


theorem analyticOnNhd_cauchyTransform (a : A) :
    AnalyticOnNhd ℂ (φ.cauchyTransform a) (resolventSet ℂ a) := by
  have hd : DifferentiableOn ℂ (φ.cauchyTransform a) (resolventSet ℂ a) :=
    fun z hz => (φ.hasDerivAt_cauchyTransform a z hz).differentiableAt.differentiableWithinAt
  exact hd.analyticOnNhd (spectrum.isOpen_resolventSet a)

end FreeProbability.StarProbabilitySpace

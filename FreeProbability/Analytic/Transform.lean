import FreeProbability.Analytic.MomentSeries
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-! # Analytic inverse moment transforms and S-transforms

The local inverse is constructed by the inverse function theorem, with its
nonzero first-moment hypothesis explicit. The S-transform has its removable
value at zero filled in using the derivative. Multiplicativity under freeness
requires additional combinatorial and free-realization results.
-/

namespace FreeProbability.StarProbabilitySpace
open scoped Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (φ : FreeProbability.StarProbabilitySpace A)

theorem analyticAt_momentGeneratingFunction_zero (a : A) :
    AnalyticAt ℂ (φ.momentGeneratingFunction a) 0 := by
  have hl : AnalyticAt ℂ (fun w : ℂ => w • a) 0 :=
    (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) a).analyticAt 0
  have hi : AnalyticAt ℂ (fun x : A => Ring.inverse (1 - x)) ((fun w : ℂ => w • a) 0) := by
    simpa only [zero_smul] using analyticAt_inverse_one_sub ℂ A
  have hs := (φ.continuousExpectation.analyticAt _).comp (hi.comp (f := fun w : ℂ => w • a) hl)
  simpa only [Function.comp_def, continuousExpectation_apply, momentGeneratingFunction, Pi.sub_apply] using!
    hs.sub (analyticAt_const (v := (1 : ℂ)))

theorem hasStrictDerivAt_momentGeneratingFunction_zero (a : A) :
    HasStrictDerivAt (φ.momentGeneratingFunction a) (φ.expectation a) 0 := by
  have hf : HasStrictDerivAt (fun w : ℂ => (1 : A) - w • a) (-a) 0 := by
    simpa only [zero_sub, one_smul] using!
      (hasStrictDerivAt_const (0 : ℂ) (1 : A)).sub ((hasStrictDerivAt_id (0 : ℂ)).smul_const a)
  have hi := (hasStrictFDerivAt_ringInverse (𝕜 := ℂ) (1 : Aˣ)).comp_hasStrictDerivAt_of_eq
    0 hf (by simp)
  have hs := (φ.continuousExpectation.hasStrictFDerivAt).comp_hasStrictDerivAt 0 hi
  simpa [Function.comp_def, momentGeneratingFunction, ContinuousLinearMap.mulLeftRight_apply] using!
    hs.sub (hasStrictDerivAt_const (0 : ℂ) (1 : ℂ))

theorem hasDerivAt_cauchyTransform (a : A) (z : ℂ) (hz : z ∈ resolventSet ℂ a) :
    HasDerivAt (φ.cauchyTransform a) (-φ.expectation ((resolvent a z) ^ 2)) z := by
  have hs := φ.continuousExpectation.hasFDerivAt.comp_hasDerivAt z
    (spectrum.hasDerivAt_resolvent_const_left hz)
  simpa only [Function.comp_def, continuousExpectation_apply, cauchyTransform, map_neg] using! hs


/-- The analytic local inverse requires a nonzero first moment. -/
noncomputable def momentInverse (a : A) (h : φ.expectation a ≠ 0) : ℂ → ℂ :=
  (φ.hasStrictDerivAt_momentGeneratingFunction_zero a).localInverse
    (φ.momentGeneratingFunction a) (φ.expectation a) 0 h

@[simp] theorem momentInverse_zero (a : A) (h : φ.expectation a ≠ 0) :
    φ.momentInverse a h 0 = 0 := by
  have hi := ((φ.hasStrictDerivAt_momentGeneratingFunction_zero a).eventually_left_inverse h).self_of_nhds
  simpa only [momentInverse, momentGeneratingFunction_zero] using hi

theorem momentInverse_eventually_left_inverse (a : A) (h : φ.expectation a ≠ 0) :
    ∀ᶠ w in 𝓝 (0 : ℂ), φ.momentInverse a h (φ.momentGeneratingFunction a w) = w :=
  (φ.hasStrictDerivAt_momentGeneratingFunction_zero a).eventually_left_inverse h

theorem momentInverse_eventually_right_inverse (a : A) (h : φ.expectation a ≠ 0) :
    ∀ᶠ w in 𝓝 (0 : ℂ), φ.momentGeneratingFunction a (φ.momentInverse a h w) = w := by
  simpa only [momentInverse, momentGeneratingFunction_zero] using
    (φ.hasStrictDerivAt_momentGeneratingFunction_zero a).eventually_right_inverse h

theorem hasStrictDerivAt_momentInverse_zero (a : A) (h : φ.expectation a ≠ 0) :
    HasStrictDerivAt (φ.momentInverse a h) (φ.expectation a)⁻¹ 0 := by
  simpa only [momentInverse, momentGeneratingFunction_zero] using
    (φ.hasStrictDerivAt_momentGeneratingFunction_zero a).to_localInverse h

theorem analyticAt_momentInverse_zero (a : A) (h : φ.expectation a ≠ 0) :
    AnalyticAt ℂ (φ.momentInverse a h) 0 := by
  have hd : deriv (φ.momentGeneratingFunction a) 0 = φ.expectation a :=
    (φ.hasStrictDerivAt_momentGeneratingFunction_zero a).hasDerivAt.deriv
  have hn : deriv (φ.momentGeneratingFunction a) 0 ≠ 0 := hd ▸ h
  have he : (φ.momentInverse a h) ∘ (φ.momentGeneratingFunction a) =ᶠ[𝓝 0] id :=
    φ.momentInverse_eventually_left_inverse a h
  have hc : AnalyticAt ℂ ((φ.momentInverse a h) ∘ (φ.momentGeneratingFunction a)) 0 :=
    analyticAt_id.congr he.symm
  have hi := (analyticAt_comp_iff_of_deriv_ne_zero
    (φ.analyticAt_momentGeneratingFunction_zero a) hn).mp hc
  simpa only [momentGeneratingFunction_zero] using hi

/-- The S-transform includes its analytic removable value at zero. -/
noncomputable def sTransform (a : A) (h : φ.expectation a ≠ 0) (w : ℂ) : ℂ :=
  (1 + w) * dslope (φ.momentInverse a h) 0 w

@[simp] theorem sTransform_zero (a : A) (h : φ.expectation a ≠ 0) :
    φ.sTransform a h 0 = (φ.expectation a)⁻¹ := by
  simp only [sTransform, add_zero, one_mul, dslope_same,
    (φ.hasStrictDerivAt_momentInverse_zero a h).hasDerivAt.deriv]

theorem sTransform_eq (a : A) (h : φ.expectation a ≠ 0) (w : ℂ) (hw : w ≠ 0) :
    φ.sTransform a h w = ((1 + w) / w) * φ.momentInverse a h w := by
  rw [sTransform, dslope_of_ne _ hw, slope_def_field, momentInverse_zero, sub_zero, sub_zero]
  ring

theorem analyticAt_sTransform_zero (a : A) (h : φ.expectation a ≠ 0) :
    AnalyticAt ℂ (φ.sTransform a h) 0 := by
  have hi := φ.analyticAt_momentInverse_zero a h
  obtain ⟨p, hp⟩ := hi
  have hs : AnalyticAt ℂ (dslope (φ.momentInverse a h) 0) 0 :=
    hp.has_fpower_series_dslope_fslope.analyticAt
  exact (analyticAt_const.add analyticAt_id).mul hs

end FreeProbability.StarProbabilitySpace

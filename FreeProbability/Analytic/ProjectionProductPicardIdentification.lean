import FreeProbability.Analytic.ProjectionProductPicardAnalytic

/-! # Identification of the Picard analytic sum with actual projection moments -/

noncomputable section
open scoped Topology
namespace FreeProbability

/-- The normalized inverse parameter of the half-projection curve. -/
def halfProjectionInverseParameter (L : ℕ) (q : ℂ) : ℂ :=
  (2 : ℂ) ^ L * q / (1 + q) ^ L

/-- The inverse parameter has a genuinely nonzero derivative at zero. -/
theorem hasStrictDerivAt_halfProjectionInverseParameter_zero (L : ℕ) :
    HasStrictDerivAt (halfProjectionInverseParameter L) ((2 : ℂ) ^ L) 0 := by
  have h := ((hasStrictDerivAt_id (0 : ℂ)).const_mul ((2 : ℂ) ^ L)).div
    (((hasStrictDerivAt_const (0 : ℂ) (1 : ℂ)).add (hasStrictDerivAt_id (0 : ℂ))).pow L)
    (by simp)
  convert h using 1
  · rfl
  · simp

/-- Two continuous normalized solutions near zero agree, by the actual local
inverse theorem. No global branch uniqueness is asserted. -/
theorem halfProjection_normalized_solution_eventually_unique (L : ℕ)
    (q Q : ℂ → ℂ) (hq : ContinuousAt q 0) (hQ : ContinuousAt Q 0)
    (hq0 : q 0 = 0) (hQ0 : Q 0 = 0)
    (hfq : ∀ᶠ z : ℂ in 𝓝 0, halfProjectionInverseParameter L (q z) = z)
    (hfQ : ∀ᶠ z : ℂ in 𝓝 0, halfProjectionInverseParameter L (Q z) = z) :
    q =ᶠ[𝓝 0] Q := by
  have hd := hasStrictDerivAt_halfProjectionInverseParameter_zero L
  have hn : (2 : ℂ) ^ L ≠ 0 := pow_ne_zero L (by norm_num)
  have htq : Filter.Tendsto q (𝓝 0) (𝓝 0) := by simpa only [hq0] using hq.tendsto
  have htQ : Filter.Tendsto Q (𝓝 0) (𝓝 0) := by simpa only [hQ0] using hQ.tendsto
  have hleft := hd.eventually_left_inverse hn
  filter_upwards [htq.eventually hleft, htQ.eventually hleft, hfq, hfQ] with z hqz hQz hfqz hfQz
  rw [hfqz] at hqz
  rw [hfQz] at hQz
  exact hqz.symm.trans hQz

private theorem parameter_eq_of_normalized_equation (L : ℕ) (z q : ℂ)
    (hq : 1 + q ≠ 0) (he : (2 : ℂ) ^ L * q = z * (1 + q) ^ L) :
    halfProjectionInverseParameter L q = z := by
  rw [halfProjectionInverseParameter, he, mul_div_cancel_right₀ _ (pow_ne_zero L hq)]

/-- The genuine constructed Picard sum satisfies the inverse-parameter
relation near zero; its continuity and normalization are proved. -/
theorem halfProjectionAnalyticSum_inverseParameter_eventually (L : ℕ) :
    ∀ᶠ z : ℂ in 𝓝 0, halfProjectionInverseParameter L (halfProjectionAnalyticSum L z) = z := by
  have hc := (analyticAt_halfProjectionAnalyticSum_zero L).continuousAt
  have hden : ∀ᶠ z : ℂ in 𝓝 0, 1 + halfProjectionAnalyticSum L z ≠ 0 :=
    (continuousAt_const.add hc).eventually_ne (by simp)
  have hsmall : ∀ᶠ z : ℂ in 𝓝 0, ‖z‖ ≤ (1 / 2 : ℝ) :=
    ((continuous_norm.continuousAt).eventually_lt
      (continuousAt_const : ContinuousAt (fun _ : ℂ => (1 / 2 : ℝ)) 0) (by norm_num)).mono (fun _ hz => hz.le)
  filter_upwards [hden, hsmall] with z hdz hsz
  apply parameter_eq_of_normalized_equation L z _ hdz
  have h := halfProjectionAnalyticSum_equation L (1 / 2) (by norm_num) 1 (by norm_num)
    (by rw [show (1 + (1 : ℝ)) = 2 by norm_num, div_mul_cancel₀ _ (pow_ne_zero L (by norm_num))]; norm_num) z hsz
  have he := congrArg (fun u : ℂ => (2 : ℂ) ^ L * u) h
  simpa only [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero L (by norm_num : (2 : ℂ) ≠ 0)), one_mul] using he

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
namespace StarProbabilitySpace
variable (φ : FreeProbability.StarProbabilitySpace A)

/-- The normalized actual resolvent moment function of a finite positive product. -/
def normalizedProjectionProductMoment (n : ℕ) (p : Fin n → A) (z : ℂ) : ℂ :=
  φ.momentGeneratingFunction (iteratedPositiveProduct n p) z /
    (1 + φ.momentGeneratingFunction (iteratedPositiveProduct n p) z)

@[simp] theorem normalizedProjectionProductMoment_zero (n : ℕ) (p : Fin n → A) :
    φ.normalizedProjectionProductMoment n p 0 = 0 := by simp [normalizedProjectionProductMoment]

theorem continuousAt_normalizedProjectionProductMoment_zero (n : ℕ) (p : Fin n → A) :
    ContinuousAt (φ.normalizedProjectionProductMoment n p) 0 :=
  (φ.analyticAt_momentGeneratingFunction_zero _).continuousAt.div
    (continuousAt_const.add (φ.analyticAt_momentGeneratingFunction_zero _).continuousAt) (by simp)

/-- The convergent nonnegative Picard series is EXACTLY the actual normalized
moment germ of the supplied free half-trace projection family. -/
theorem normalizedProjectionProductMoment_eq_picard_eventually
    (hφ : IsTracial φ.toProbabilitySpace) (n : ℕ) {B : Fin (n + 1) → Subalgebra ℂ A}
    (hf : FreelyIndependent φ.toProbabilitySpace B) (p : Fin (n + 1) → A)
    (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, IsStarProjection (p i))
    (hE : ∀ i, φ.expectation (p i) = (1 / 2 : ℂ)) :
    φ.normalizedProjectionProductMoment (n + 1) p =ᶠ[𝓝 0] halfProjectionAnalyticSum (n + 1) := by
  apply halfProjection_normalized_solution_eventually_unique (n + 1)
    (φ.normalizedProjectionProductMoment (n + 1) p) (halfProjectionAnalyticSum (n + 1))
    (φ.continuousAt_normalizedProjectionProductMoment_zero _ _)
    (analyticAt_halfProjectionAnalyticSum_zero _).continuousAt
    (φ.normalizedProjectionProductMoment_zero _ _) (halfProjectionAnalyticSum_zero _)
  · have hc := φ.continuousAt_normalizedProjectionProductMoment_zero (n + 1) p
    have hden : ∀ᶠ z : ℂ in 𝓝 0, 1 + φ.normalizedProjectionProductMoment (n + 1) p z ≠ 0 :=
      (continuousAt_const.add hc).eventually_ne (by simp)
    filter_upwards [hden, φ.normalizedMoment_iteratedHalfProjectionProduct_equation_eventually
      hφ n hf p hpB hp hE] with z hz he
    exact parameter_eq_of_normalized_equation (n + 1) z _ hz he
  · exact halfProjectionAnalyticSum_inverseParameter_eventually (n + 1)
/-- The actual moment-function germ is the genuine analytic Picard sum
under the inverse normalization, not a merely formal power series. -/
theorem momentGeneratingFunction_eq_picard_fraction_eventually
    (hφ : IsTracial φ.toProbabilitySpace) (n : ℕ) {B : Fin (n + 1) → Subalgebra ℂ A}
    (hf : FreelyIndependent φ.toProbabilitySpace B) (p : Fin (n + 1) → A)
    (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, IsStarProjection (p i))
    (hE : ∀ i, φ.expectation (p i) = (1 / 2 : ℂ)) :
    φ.momentGeneratingFunction (iteratedPositiveProduct (n + 1) p) =ᶠ[𝓝 0]
      (fun z => halfProjectionAnalyticSum (n + 1) z / (1 - halfProjectionAnalyticSum (n + 1) z)) := by
  have hden : ∀ᶠ z : ℂ in 𝓝 0,
      1 + φ.momentGeneratingFunction (iteratedPositiveProduct (n + 1) p) z ≠ 0 :=
    (continuousAt_const.add (φ.analyticAt_momentGeneratingFunction_zero _).continuousAt).eventually_ne (by simp)
  filter_upwards [φ.normalizedProjectionProductMoment_eq_picard_eventually hφ n hf p hpB hp hE,
    hden] with z hz hd
  rw [← hz]
  unfold normalizedProjectionProductMoment
  let w := φ.momentGeneratingFunction (iteratedPositiveProduct (n + 1) p) z
  change w = (w / (1 + w)) / (1 - w / (1 + w))
  have hdw : 1 + w ≠ 0 := hd
  have hid : 1 - w / (1 + w) = (1 + w)⁻¹ := by
    field_simp [hdw]
    ring
  rw [hid, div_eq_mul_inv, inv_inv, div_mul_cancel₀ _ hd]
end StarProbabilitySpace
end FreeProbability

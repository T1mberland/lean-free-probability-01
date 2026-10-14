import FreeProbability.Analytic.ProjectionProductPhysicalCurve

/-! # Selection of the genuine physical branch by analytic Picard matching -/

noncomputable section
open scoped Topology NNReal ENNReal
namespace FreeProbability

/-- Subcritical parameters have a scalar supersolution strictly below the
normalized critical point, not merely below one. -/
theorem exists_halfProjection_physical_supersolution (L : ℕ) (hL : 2 ≤ L)
    (t : ℝ) (ht : t < halfProjectionMomentThreshold L) :
    ∃ r : ℝ, 0 < r ∧ r < halfProjectionCriticalQ L ∧ (t / (2 : ℝ) ^ L) * (1 + r) ^ L ≤ r := by
  have hr0 := halfProjectionCriticalQ_pos L hL
  have hc : ContinuousAt (halfProjectionQParameter L) (halfProjectionCriticalQ L) := by
    have hn : ContinuousAt (fun q : ℝ => (2 : ℝ) ^ L * q) (halfProjectionCriticalQ L) :=
      continuousAt_const.mul continuousAt_id
    have hd : ContinuousAt (fun q : ℝ => (1 + q) ^ L) (halfProjectionCriticalQ L) :=
      (continuousAt_const.add continuousAt_id).pow L
    exact hn.div hd (pow_ne_zero L (by linarith))
  have hnear : ∀ᶠ r in 𝓝 (halfProjectionCriticalQ L), t < halfProjectionQParameter L r ∧ 0 < r :=
    ((continuousAt_const : ContinuousAt (fun _ : ℝ => t) (halfProjectionCriticalQ L)).eventually_lt hc
      (by rw [halfProjectionQParameter_at_critical L hL]; exact ht)).and
      ((continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) (halfProjectionCriticalQ L)).eventually_lt
        continuousAt_id hr0)
  obtain ⟨r, hrcrit, htr, hr⟩ := hnear.exists_lt
  refine ⟨r, hr, hrcrit, ?_⟩
  have hden : 0 < (1 + r) ^ L := pow_pos (by linarith) L
  have htwo : 0 < (2 : ℝ) ^ L := pow_pos (by norm_num) L
  have hnum : t * (1 + r) ^ L < (2 : ℝ) ^ L * r := (lt_div_iff₀ hden).mp htr
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ htwo).mpr (by simpa only [mul_comm] using hnum.le)

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
namespace StarProbabilitySpace
variable (φ : FreeProbability.StarProbabilitySpace A)

/-- The genuine analytic Picard reciprocal identity continues throughout
its shared disk with the TRUE law moment series. -/
theorem lawMomentSum_picard_product_on_disk
    (hφ : IsTracial φ.toProbabilitySpace) (n : ℕ) {B : Fin (n + 1) → Subalgebra ℂ A}
    (hf : FreelyIndependent φ.toProbabilitySpace B) (p : Fin (n + 1) → A)
    (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, IsStarProjection (p i))
    (hE : ∀ i, φ.expectation (p i) = (1 / 2 : ℂ))
    (t : ℝ≥0) (ht : 0 < t) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hsuper : ((t : ℝ) / (2 : ℝ) ^ (n + 1)) * (1 + r) ^ (n + 1) ≤ r)
    (s : ℝ≥0) (hs : 0 < s) (hst : s < t) (z : ℂ) (hz : ‖z‖ < s) :
    (1 - halfProjectionAnalyticSum (n + 1) z) *
      φ.lawMomentSum (iteratedPositiveProduct (n + 1) p) z = 1 := by
  let a := iteratedPositiveProduct (n + 1) p
  have hrad := φ.expectationInverseTaylorSeries_iteratedHalfProjection_radius_bound hφ n hf p hpB hp hE
    t ht r hr hr1 hsuper s hs hst
  let F := fun y : ℂ => (1 - halfProjectionAnalyticSum (n + 1) y) * φ.lawMomentSum a y - 1
  have hF : AnalyticOnNhd ℂ F (Metric.ball 0 s) := by
    intro y hy
    have hys : ‖y‖ < s := by simpa only [Metric.mem_ball, dist_zero_right] using hy
    have hQ := (halfProjectionAnalyticSum_hasFPowerSeries (n + 1) t ht r hr hsuper).analyticAt_of_mem
      (by simp only [Metric.mem_eball, edist_zero_right];
          exact (ENNReal.coe_lt_coe.mpr (show ‖y‖₊ < t by exact_mod_cast (hys.trans (by exact_mod_cast hst)))))
    have hI := (φ.expectationInverseTaylorSeries a).analyticOnNhd y
      (show y ∈ Metric.eball 0 (φ.expectationInverseTaylorSeries a).radius by
        simp only [Metric.mem_eball, edist_zero_right]
        exact (ENNReal.coe_lt_coe.mpr (show ‖y‖₊ < s by exact_mod_cast hys)).trans_le hrad)
    exact ((analyticAt_const.sub hQ).mul hI).sub analyticAt_const
  have hden : ∀ᶠ y : ℂ in 𝓝 0, 1 - halfProjectionAnalyticSum (n + 1) y ≠ 0 :=
    (continuousAt_const.sub (analyticAt_halfProjectionAnalyticSum_zero _).continuousAt).eventually_ne (by simp)
  have hevent : F =ᶠ[𝓝 0] 0 := by
    filter_upwards [φ.lawMomentSum_eq_expectation_inverse_eventually a,
      φ.expectation_inverse_eq_picard_reciprocal_eventually hφ n hf p hpB hp hE, hden] with y hy he hd
    change (1 - halfProjectionAnalyticSum (n + 1) y) * φ.lawMomentSum a y - 1 = 0
    rw [hy, he, halfProjectionInverseMomentSum, mul_one_div_cancel hd, sub_self]
  have hzero := hF.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball (0 : ℂ) (s : ℝ)).isPreconnected (by simp; exact_mod_cast hs) hevent
  exact sub_eq_zero.mp (hzero (by simpa only [Metric.mem_ball, dist_zero_right] using hz))

/-- The ACTUAL Cauchy parameter lies on the physical normalized branch
throughout the full right exterior, including the length-two boundary. -/
theorem halfProjectionExteriorW_physical_interval
    (hφ : IsTracial φ.toProbabilitySpace) (L : ℕ) (hL : 2 ≤ L)
    {B : Fin L → Subalgebra ℂ A} (hf : FreelyIndependent φ.toProbabilitySpace B)
    (p : Fin L → A) (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, IsStarProjection (p i))
    (hE : ∀ i, φ.expectation (p i) = (1 / 2 : ℂ)) (x : ℝ) (hx : halfProjectionRightEdge L < x) :
    let w := φ.halfProjectionExteriorW L p hp x
    0 < w / (1 + w) ∧ w / (1 + w) < halfProjectionCriticalQ L := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, L = n + 1 := ⟨L - 1, (Nat.sub_add_cancel (by omega)).symm⟩
  let w := φ.halfProjectionExteriorW (n + 1) p hp x
  have hw : 0 < w := φ.halfProjectionExteriorW_pos hφ _ hL hf p hpB hp hE x hx
  have hq : 0 < w / (1 + w) := div_pos hw (by linarith)
  refine ⟨hq, ?_⟩
  have hx0 : 0 < x := (halfProjectionRightEdge_pos _ hL).trans hx
  have hu : 0 < 1 / x := one_div_pos.mpr hx0
  have huthresh : 1 / x < halfProjectionMomentThreshold (n + 1) := by
    rw [halfProjectionMomentThreshold_eq_reciprocal]
    exact one_div_lt_one_div_of_lt (halfProjectionRightEdge_pos _ hL) hx
  obtain ⟨t, hut, htc⟩ := exists_between huthresh
  have ht0 : 0 < t := hu.trans hut
  obtain ⟨r, hr, hrc, hsuper⟩ := exists_halfProjection_physical_supersolution (n + 1) hL t htc
  have hr1 : r < 1 := hrc.trans_le (halfProjectionCriticalQ_le_one _ hL)
  obtain ⟨s, hus, hst⟩ := exists_between hut
  have hs0 : 0 < s := hu.trans hus
  let tN : ℝ≥0 := ⟨t, ht0.le⟩
  let sN : ℝ≥0 := ⟨s, hs0.le⟩
  have hprod := φ.lawMomentSum_picard_product_on_disk hφ n hf p hpB hp hE tN
    (by exact_mod_cast ht0) r hr.le hr1 hsuper sN (by exact_mod_cast hs0)
    (by exact_mod_cast hst) ((1 / x : ℝ) : ℂ)
    (by change ‖((1 / x : ℝ) : ℂ)‖ < s; simpa only [Complex.norm_real, Real.norm_of_nonneg hu.le] using hus)
  let a := iteratedPositiveProduct (n + 1) p
  have ha : 0 ≤ a := iteratedPositiveProduct_nonneg _ p (fun i => (hp i).nonneg)
  rw [φ.lawMomentSum_ofReal a ha.isSelfAdjoint (1 / x)] at hprod
  have hI : φ.lawRealMomentSum a ha.isSelfAdjoint (1 / x) = 1 + w := by
    unfold w halfProjectionExteriorW
    rw [φ.iteratedHalfProjection_realCauchyTransform_eq_momentSum hφ _ hL hf p hpB hp hE x hx]
    ring
  rw [hI] at hprod
  have hQ : halfProjectionAnalyticSum (n + 1) ((1 / x : ℝ) : ℂ) = ((w / (1 + w) : ℝ) : ℂ) := by
    push_cast at hprod ⊢
    apply (eq_div_iff (by exact_mod_cast (show 1 + w ≠ 0 by linarith))).mpr
    linear_combination -hprod
  have hnorm := halfProjectionAnalyticSum_norm_le (n + 1) t ht0.le r hr.le hsuper
    ((1 / x : ℝ) : ℂ) (by simpa only [Complex.norm_real, Real.norm_of_nonneg hu.le] using hut.le)
  rw [hQ, Complex.norm_real, Real.norm_of_nonneg hq.le] at hnorm
  exact hnorm.trans_lt hrc
end StarProbabilitySpace
end FreeProbability

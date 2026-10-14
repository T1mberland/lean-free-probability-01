import FreeProbability.Analytic.ProjectionProductLawMomentBounds

/-! # The supercritical moment obstruction reaches actual probability support -/

noncomputable section
open MeasureTheory
open scoped Topology NNReal ENNReal
namespace FreeProbability

private theorem qParameter_eq_of_moment_polynomial (n : ℕ) (u I : ℝ) (hI : 1 ≤ I)
    (he : u * (I - (1 / 2 : ℝ)) ^ (n + 1) = (I - 1) * I ^ n) :
    halfProjectionQParameter (n + 1) ((I - 1) / I) = u := by
  have hI0 : I ≠ 0 := by linarith
  have hq1 : 1 + (I - 1) / I = (2 * I - 1) / I := by field_simp; ring
  have h2 : 2 * I - 1 ≠ 0 := by linarith
  have hhalf : I * 2 - 1 = (2 : ℝ) * (I - (1 / 2 : ℝ)) := by ring
  unfold halfProjectionQParameter
  rw [hq1, div_pow]
  apply (div_eq_iff (div_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ hI0))).mpr
  rw [div_eq_mul_inv]
  field_simp [hI0]
  rw [hhalf, mul_pow, pow_succ I]
  have hscaled := congrArg (fun x : ℝ => (2 : ℝ) ^ (n + 1) * I * x) he
  nlinarith only [hscaled]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
namespace StarProbabilitySpace
variable (φ : FreeProbability.StarProbabilitySpace A)

/-- The actual law cannot have a strictly smaller positive right support
bound than the proposed edge. The proof uses TRUE law moments and analytic
continuation, not an ambient inverse outside its resolvent domain. -/
theorem iteratedHalfProjection_law_not_supported_below_edge
    (hφ : IsTracial φ.toProbabilitySpace) (L : ℕ) (hL : 2 ≤ L)
    {B : Fin L → Subalgebra ℂ A} (hf : FreelyIndependent φ.toProbabilitySpace B)
    (p : Fin L → A) (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, IsStarProjection (p i))
    (hE : ∀ i, φ.expectation (p i) = (1 / 2 : ℂ))
    (b : ℝ) (hb : 0 < b) (hbedge : b < halfProjectionRightEdge L) :
    ¬ (iteratedPositiveProbabilityLaw φ L p (fun i => (hp i).nonneg) : Measure ℝ).support ⊆ Set.Iic b := by
  intro hsupport
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, L = n + 1 := ⟨L - 1, (Nat.sub_add_cancel (by omega)).symm⟩
  let a := iteratedPositiveProduct (n + 1) p
  have hapos : 0 ≤ a := iteratedPositiveProduct_nonneg _ p (fun i => (hp i).nonneg)
  have hspecsupport : (spectralMeasure φ hapos.isSelfAdjoint).support ⊆ Set.Iic b := hsupport
  have htcrit : halfProjectionMomentThreshold (n + 1) < 1 / b := by
    rw [halfProjectionMomentThreshold_eq_reciprocal]
    exact one_div_lt_one_div_of_lt hb hbedge
  obtain ⟨u, hucrit, hub⟩ := exists_between htcrit
  obtain ⟨s, hus, hsb⟩ := exists_between hub
  have hu : 0 < u := (halfProjectionMomentThreshold_pos _ hL).trans hucrit
  have hs : 0 < s := hu.trans hus
  let sN : ℝ≥0 := ⟨s, hs.le⟩
  have hrad := φ.expectationInverseTaylorSeries_radius_of_spectral_support a hapos b hb.le
    hspecsupport sN ((lt_div_iff₀ hb).mp hsb)
  have hpoly := φ.lawMomentSum_iteratedHalfProjection_equation_on_disk hφ n hf p hpB hp hE
    sN (by exact_mod_cast hs) hrad (u : ℂ)
    (by change ‖(u : ℂ)‖ < s; simpa only [Complex.norm_real, Real.norm_of_nonneg hu.le] using hus)
  let μ := spectralProbabilityMeasure φ hapos.isSelfAdjoint
  have hpos : ∀ᵐ x ∂(μ : Measure ℝ), 0 ≤ x := by
    have hsupp : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ (μ : Measure ℝ).support := Measure.support_mem_ae
    filter_upwards [hsupp] with x hx
    exact spectrum_nonneg_of_nonneg hapos (spectralMeasure_support_subset φ hapos.isSelfAdjoint hx)
  have hsum := summable_positive_moments_of_support_bound μ hpos
    (spectralMeasure_integrable_pow φ hapos.isSelfAdjoint) b hb.le hspecsupport u hu.le
    ((lt_div_iff₀ hb).mp hub)
  have hsumReal : Summable (fun k : ℕ =>
      (∫ x : ℝ, x ^ k ∂spectralMeasure φ hapos.isSelfAdjoint) * u ^ k) := by
    convert hsum using 1
    funext k
    dsimp [μ, spectralProbabilityMeasure]
    ring
  let I := φ.lawRealMomentSum a hapos.isSelfAdjoint u
  have hI : 1 ≤ I := φ.lawRealMomentSum_ge_one a hapos u hu.le hsumReal
  rw [φ.lawMomentSum_ofReal a hapos.isSelfAdjoint u] at hpoly
  change (u : ℂ) * ((I : ℂ) - (1 / 2 : ℂ)) ^ (n + 1) = ((I : ℂ) - 1) * (I : ℂ) ^ n at hpoly
  have hpolyReal : u * (I - (1 / 2 : ℝ)) ^ (n + 1) = (I - 1) * I ^ n := by
    apply Complex.ofReal_injective
    push_cast
    exact hpoly
  have hparam := qParameter_eq_of_moment_polynomial n u I hI hpolyReal
  have hq : 0 ≤ (I - 1) / I := div_nonneg (by linarith) (by linarith)
  have hmax := halfProjectionQParameter_le_threshold (n + 1) hL ((I - 1) / I) hq
  rw [hparam] at hmax
  exact (not_le_of_gt hucrit) hmax
/-- The intended edge is the greatest point of the ACTUAL probability-law
support for every supplied free half-projection family, including length
two. This is a support theorem, with no faithfulness hypothesis. -/
theorem iteratedHalfProjection_law_support_isGreatest
    (hφ : IsTracial φ.toProbabilitySpace) (L : ℕ) (hL : 2 ≤ L)
    {B : Fin L → Subalgebra ℂ A} (hf : FreelyIndependent φ.toProbabilitySpace B)
    (p : Fin L → A) (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, IsStarProjection (p i))
    (hE : ∀ i, φ.expectation (p i) = (1 / 2 : ℂ)) :
    IsGreatest (iteratedPositiveProbabilityLaw φ L p (fun i => (hp i).nonneg) : Measure ℝ).support
      (halfProjectionRightEdge L) := by
  let μ := iteratedPositiveProbabilityLaw φ L p (fun i => (hp i).nonneg)
  have hc : IsCompact (μ : Measure ℝ).support := iteratedPositiveProbabilityLaw_isCompact_support φ L p _
  have hne : (μ : Measure ℝ).support.Nonempty := Measure.nonempty_support (IsProbabilityMeasure.ne_zero _)
  have hg := hc.isGreatest_sSup hne
  have hupper := φ.iteratedHalfProjection_law_support_sharp_upper hφ L hL hf p hpB hp hE
  have hsuple : sSup (μ : Measure ℝ).support ≤ halfProjectionRightEdge L := hupper hg.1
  have hedgele : halfProjectionRightEdge L ≤ sSup (μ : Measure ℝ).support := by
    by_contra hn
    have hsup : sSup (μ : Measure ℝ).support < halfProjectionRightEdge L := lt_of_not_ge hn
    have hmax : max 0 (sSup (μ : Measure ℝ).support) < halfProjectionRightEdge L :=
      max_lt_iff.mpr ⟨halfProjectionRightEdge_pos L hL, hsup⟩
    obtain ⟨b, hmb, hbe⟩ := exists_between hmax
    have hb : 0 < b := (le_max_left 0 _).trans_lt hmb
    have hsupport : (μ : Measure ℝ).support ⊆ Set.Iic b := by
      intro x hx
      exact (hg.2 hx).trans ((le_max_right 0 _).trans hmb.le)
    exact φ.iteratedHalfProjection_law_not_supported_below_edge hφ L hL hf p hpB hp hE b hb hbe hsupport
  have heq : sSup (μ : Measure ℝ).support = halfProjectionRightEdge L := le_antisymm hsuple hedgele
  rw [← heq]
  exact hg

/-- The actual right support edge equals `L^L/(2^L*(L-1)^(L-1))`.
Physical exterior parameter selection is a separate theorem. -/
theorem iteratedHalfProjection_law_right_edge
    (hφ : IsTracial φ.toProbabilitySpace) (L : ℕ) (hL : 2 ≤ L)
    {B : Fin L → Subalgebra ℂ A} (hf : FreelyIndependent φ.toProbabilitySpace B)
    (p : Fin L → A) (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, IsStarProjection (p i))
    (hE : ∀ i, φ.expectation (p i) = (1 / 2 : ℂ)) :
    sSup (iteratedPositiveProbabilityLaw φ L p (fun i => (hp i).nonneg) : Measure ℝ).support =
      halfProjectionRightEdge L := by
  have h := φ.iteratedHalfProjection_law_support_isGreatest hφ L hL hf p hpB hp hE
  exact h.isLUB.csSup_eq ⟨_, h.1⟩
end StarProbabilitySpace
end FreeProbability

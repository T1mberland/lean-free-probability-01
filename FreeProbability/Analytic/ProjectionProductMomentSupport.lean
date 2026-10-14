import FreeProbability.Analytic.ProjectionProductLaw
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Genuine support bounds from summable positive moment series -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace FreeProbability

/-- Summable integrals of norms force pointwise summability almost everywhere.
This is a Tonelli argument, with no assumed support bound. -/
theorem ae_summable_of_summable_integral_norm {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [CompleteSpace E]
    (μ : Measure X) (F : ℕ → X → E) (hF : ∀ n, Integrable (F n) μ)
    (hs : Summable (fun n => ∫ x, ‖F n x‖ ∂μ)) :
    ∀ᵐ x ∂μ, Summable (fun n => F n x) := by
  have hco (n : ℕ) : (∫⁻ x, ‖F n x‖ₑ ∂μ) = ‖∫ x, ‖F n x‖ ∂μ‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hF n).norm, ENNReal.coe_nnreal_eq, coe_nnnorm,
      Real.norm_of_nonneg (integral_nonneg (fun x => norm_nonneg (F n x)))]
    simp only [coe_nnnorm]
  have hsum : (∫⁻ x, ∑' n, ‖F n x‖ₑ ∂μ) ≠ ∞ := by
    rw [lintegral_tsum (fun n => (hF n).aestronglyMeasurable.enorm), funext hco]
    exact tsum_enorm_ne_top_iff_summable_norm.mpr hs.abs
  filter_upwards [ae_lt_top' (AEMeasurable.tsum (fun n =>
    (hF n).aestronglyMeasurable.enorm)) hsum] with x hx
  exact (tsum_enorm_ne_top_iff_summable_norm.mp hx.ne).of_norm

/-- A genuinely summable positive moment series bounds the actual support.
The conclusion comes from pointwise geometric summability, not from a
hypothesis identifying the proposed spectral edge. -/
theorem support_subset_Iic_of_summable_positive_moments (μ : Measure ℝ)
    (hpos : ∀ᵐ x ∂μ, 0 ≤ x) (hint : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) μ)
    (t : ℝ) (ht : 0 < t)
    (hs : Summable (fun n : ℕ => t ^ n * ∫ x : ℝ, x ^ n ∂μ)) :
    μ.support ⊆ Set.Iic (1 / t) := by
  have hF (n : ℕ) : Integrable (fun x : ℝ => (t * x) ^ n) μ := by
    simpa only [mul_pow] using (hint n).const_mul (t ^ n)
  have hsNorm : Summable (fun n : ℕ => ∫ x : ℝ, ‖(t * x) ^ n‖ ∂μ) := by
    convert hs using 1
    ext n
    rw [integral_congr_ae (hpos.mono (fun x hx =>
      Real.norm_of_nonneg (pow_nonneg (mul_nonneg ht.le hx) n)))]
    simp only [mul_pow, integral_const_mul]
  have hae := ae_summable_of_summable_integral_norm μ (fun n x => (t * x) ^ n) hF hsNorm
  apply Measure.support_subset_of_isClosed isClosed_Iic
  filter_upwards [hae] with x hx
  have hlt : ‖t * x‖ < 1 := summable_geometric_iff_norm_lt_one.mp hx
  have htx : t * x < 1 := (le_abs_self (t * x)).trans_lt hlt
  exact le_of_lt ((lt_div_iff₀ ht).mpr (by simpa only [mul_comm] using htx))

/-- Conversely an actual support bound gives genuine moment-series
summability strictly inside the reciprocal support bound. -/
theorem summable_positive_moments_of_support_bound (μ : ProbabilityMeasure ℝ)
    (hpos : ∀ᵐ x ∂(μ : Measure ℝ), 0 ≤ x)
    (hint : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) (μ : Measure ℝ))
    (b : ℝ) (hb : 0 ≤ b) (hbound : (μ : Measure ℝ).support ⊆ Set.Iic b)
    (t : ℝ) (ht : 0 ≤ t) (htb : t * b < 1) :
    Summable (fun n : ℕ => t ^ n * ∫ x : ℝ, x ^ n ∂(μ : Measure ℝ)) := by
  have hgeom : Summable (fun n : ℕ => (t * b) ^ n) :=
    summable_geometric_of_lt_one (mul_nonneg ht hb) htb
  apply hgeom.of_norm_bounded
  intro n
  have hm0 : 0 ≤ ∫ x : ℝ, x ^ n ∂(μ : Measure ℝ) :=
    integral_nonneg_of_ae (hpos.mono (fun x hx => pow_nonneg hx n))
  have hsupp : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ (μ : Measure ℝ).support := Measure.support_mem_ae
  have hmn : (∫ x : ℝ, x ^ n ∂(μ : Measure ℝ)) ≤ b ^ n := by
    calc
      _ ≤ ∫ _ : ℝ, b ^ n ∂(μ : Measure ℝ) := by
        apply integral_mono_ae (hint n) (integrable_const _)
        filter_upwards [hpos, hsupp] with x hx hxs
        exact pow_le_pow_left₀ hx (hbound hxs) n
      _ = b ^ n := by simp
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg ht n) hm0), mul_pow]
  exact mul_le_mul_of_nonneg_left hmn (pow_nonneg ht n)

/-- Summability at every parameter below the candidate reciprocal edge
forces the genuine right support bound. No analyticity surrogate is used. -/
theorem support_subset_Iic_of_subcritical_moment_summability (μ : Measure ℝ)
    (hpos : ∀ᵐ x ∂μ, 0 ≤ x) (hint : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) μ)
    (b : ℝ) (hb : 0 < b)
    (hs : ∀ t : ℝ, 0 < t → t < 1 / b →
      Summable (fun n : ℕ => t ^ n * ∫ x : ℝ, x ^ n ∂μ)) :
    μ.support ⊆ Set.Iic b := by
  intro x hx
  change x ≤ b
  apply le_of_forall_gt_imp_ge_of_dense
  intro r hr
  have hr0 : 0 < r := hb.trans hr
  have ht : 1 / r < 1 / b := one_div_lt_one_div_of_lt hb hr
  have h := support_subset_Iic_of_summable_positive_moments μ hpos hint (1 / r)
    (one_div_pos.mpr hr0) (hs (1 / r) (one_div_pos.mpr hr0) ht) hx
  simpa using h

/-- For a positive probability law with all moments integrable, its actual
right support bound is equivalent to subcritical moment summability. -/
theorem support_subset_Iic_iff_subcritical_moment_summability (μ : ProbabilityMeasure ℝ)
    (hpos : ∀ᵐ x ∂(μ : Measure ℝ), 0 ≤ x)
    (hint : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) (μ : Measure ℝ))
    (b : ℝ) (hb : 0 < b) :
    (μ : Measure ℝ).support ⊆ Set.Iic b ↔
      ∀ t : ℝ, 0 < t → t < 1 / b →
        Summable (fun n : ℕ => t ^ n * ∫ x : ℝ, x ^ n ∂(μ : Measure ℝ)) := by
  constructor
  · intro hbound t ht htb
    exact summable_positive_moments_of_support_bound μ hpos hint b hb.le hbound t ht.le
      ((lt_div_iff₀ hb).mp htb)
  · exact support_subset_Iic_of_subcritical_moment_summability (μ : Measure ℝ) hpos hint b hb

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The support bound applies to the genuine law of the actual finite
positive product whenever its true moment series is summable. -/
theorem iteratedPositiveProbabilityLaw_support_of_summable_moments
    (φ : StarProbabilitySpace A) (n : ℕ) (p : Fin n → A) (hp : ∀ i, 0 ≤ p i)
    (t : ℝ) (ht : 0 < t)
    (hs : Summable (fun k : ℕ => t ^ k *
      ∫ x : ℝ, x ^ k ∂(iteratedPositiveProbabilityLaw φ n p hp : Measure ℝ))) :
    (iteratedPositiveProbabilityLaw φ n p hp : Measure ℝ).support ⊆ Set.Iic (1 / t) := by
  apply support_subset_Iic_of_summable_positive_moments _ _ _ t ht hs
  · have hsupp : ∀ᵐ x ∂(iteratedPositiveProbabilityLaw φ n p hp : Measure ℝ),
        x ∈ (iteratedPositiveProbabilityLaw φ n p hp : Measure ℝ).support := Measure.support_mem_ae
    exact hsupp.mono (fun _ hx => iteratedPositiveProbabilityLaw_support_nonneg φ n p hp hx)
  · exact spectralMeasure_integrable_pow φ (iteratedPositiveProduct_nonneg n p hp).isSelfAdjoint
end FreeProbability

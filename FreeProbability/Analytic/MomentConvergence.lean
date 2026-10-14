import FreeProbability.Analytic.MomentSeries
import Mathlib.Analysis.Normed.Group.Tannery

/-! # From converging moments to converging analytic transforms

An eventual uniform operator-norm bound gives a geometric majorant. Dominated
convergence for series then gives convergence of the actual inverse and
resolvent expectations. Source algebras may vary and the filter is arbitrary.
-/

namespace FreeProbability.StarProbabilitySpace
open scoped Topology
variable {ι : Type*} {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {B : ι → Type*} [∀ i, CStarAlgebra (B i)] [∀ i, PartialOrder (B i)] [∀ i, StarOrderedRing (B i)]
    (φ : FreeProbability.StarProbabilitySpace A)
    (ψ : ∀ i, FreeProbability.StarProbabilitySpace (B i))

theorem tendsto_cauchyTransform_of_powerMoments (a : A) (b : ∀ i, B i) (l : Filter ι)
    (hm : ∀ k : ℕ, Filter.Tendsto (fun i => (ψ i).expectation (b i ^ k)) l (𝓝 (φ.expectation (a ^ k))))
    (R : ℝ) (hR : 0 ≤ R) (hbound : ∀ᶠ i in l, ‖b i‖ ≤ R)
    (z : ℂ) (hz : R < ‖z‖) (ha : ‖a‖ < ‖z‖) :
    Filter.Tendsto (fun i => (ψ i).cauchyTransform (b i) z) l (𝓝 (φ.cauchyTransform a z)) := by
  have hn : 0 < ‖z‖ := hR.trans_lt hz
  have hq : R / ‖z‖ < 1 := (div_lt_one hn).mpr hz
  have hg := (hasSum_geometric_of_lt_one (div_nonneg hR (norm_nonneg z)) hq).mul_left (1 / ‖z‖)
  have hb : ∀ᶠ i in l, ∀ k : ℕ,
      ‖(ψ i).expectation (b i ^ k) / z ^ (k + 1)‖ ≤ (1 / ‖z‖) * (R / ‖z‖) ^ k := by
    filter_upwards [hbound] with i hi
    intro k
    rw [norm_div, norm_pow]
    calc
      _ ≤ R ^ k / ‖z‖ ^ (k + 1) := div_le_div_of_nonneg_right
        (((ψ i).expectation_pow_norm_le (b i) k).trans (pow_le_pow_left₀ (norm_nonneg _) hi k))
        (pow_nonneg hn.le _)
      _ = _ := by rw [div_pow, pow_succ]; field_simp
  have ht := tendsto_tsum_of_dominated_convergence hg.summable
    (fun k => (hm k).div_const (z ^ (k + 1))) hb
  change Filter.Tendsto (fun i => ∑' k : ℕ, (ψ i).expectation (b i ^ k) / z ^ (k + 1)) l
    (𝓝 (∑' k : ℕ, φ.expectation (a ^ k) / z ^ (k + 1))) at ht
  rw [(φ.hasSum_cauchyTransform a z ha).tsum_eq] at ht
  apply ht.congr'
  filter_upwards [hbound] with i hi
  exact ((ψ i).hasSum_cauchyTransform (b i) z (hi.trans_lt hz)).tsum_eq


theorem tendsto_expectation_inverse_of_powerMoments (a : A) (b : ∀ i, B i) (l : Filter ι)
    (hm : ∀ k : ℕ, Filter.Tendsto (fun i => (ψ i).expectation (b i ^ k)) l (𝓝 (φ.expectation (a ^ k))))
    (R : ℝ) (hR : 0 ≤ R) (hbound : ∀ᶠ i in l, ‖b i‖ ≤ R)
    (w : ℂ) (hw : ‖w‖ * R < 1) (ha : ‖w‖ * ‖a‖ < 1) :
    Filter.Tendsto (fun i => (ψ i).expectation (Ring.inverse (1 - w • b i))) l
      (𝓝 (φ.expectation (Ring.inverse (1 - w • a)))) := by
  have hg := hasSum_geometric_of_lt_one (mul_nonneg (norm_nonneg w) hR) hw
  have hb : ∀ᶠ i in l, ∀ k : ℕ,
      ‖w ^ k * (ψ i).expectation (b i ^ k)‖ ≤ (‖w‖ * R) ^ k := by
    filter_upwards [hbound] with i hi
    intro k
    rw [norm_mul, norm_pow, mul_pow]
    exact mul_le_mul_of_nonneg_left
      (((ψ i).expectation_pow_norm_le (b i) k).trans (pow_le_pow_left₀ (norm_nonneg _) hi k))
      (pow_nonneg (norm_nonneg w) k)
  have ht := tendsto_tsum_of_dominated_convergence hg.summable
    (fun k => (hm k).const_mul (w ^ k)) hb
  change Filter.Tendsto (fun i => ∑' k : ℕ, w ^ k * (ψ i).expectation (b i ^ k)) l
    (𝓝 (∑' k : ℕ, w ^ k * φ.expectation (a ^ k))) at ht
  rw [(φ.hasSum_expectation_inverse a w ha).tsum_eq] at ht
  apply ht.congr'
  filter_upwards [hbound] with i hi
  exact ((ψ i).hasSum_expectation_inverse (b i) w
    ((mul_le_mul_of_nonneg_left hi (norm_nonneg w)).trans_lt hw)).tsum_eq

theorem tendsto_momentGeneratingFunction_of_powerMoments (a : A) (b : ∀ i, B i) (l : Filter ι)
    (hm : ∀ k : ℕ, Filter.Tendsto (fun i => (ψ i).expectation (b i ^ k)) l (𝓝 (φ.expectation (a ^ k))))
    (R : ℝ) (hR : 0 ≤ R) (hbound : ∀ᶠ i in l, ‖b i‖ ≤ R)
    (w : ℂ) (hw : ‖w‖ * R < 1) (ha : ‖w‖ * ‖a‖ < 1) :
    Filter.Tendsto (fun i => (ψ i).momentGeneratingFunction (b i) w) l
      (𝓝 (φ.momentGeneratingFunction a w)) := by
  simpa only [momentGeneratingFunction] using
    (φ.tendsto_expectation_inverse_of_powerMoments ψ a b l hm R hR hbound w hw ha).sub_const 1

end FreeProbability.StarProbabilitySpace

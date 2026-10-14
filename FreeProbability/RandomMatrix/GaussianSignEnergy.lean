import FreeProbability.RandomMatrix.ArrayCompleteConvergence
import FreeProbability.RandomMatrix.OrthogonalGaussianDirection
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-! # Gaussian positive-sign energies under arbitrary width couplings -/

namespace FreeProbability.Orthogonal

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

/-- The square of the positive part, including zero. -/
noncomputable def positiveSquared (x : ℝ) : ℝ := (max 0 x) ^ 2

@[fun_prop] theorem continuous_positiveSquared : Continuous positiveSquared := by
  unfold positiveSquared
  fun_prop

theorem positiveSquared_le_sq (x : ℝ) : positiveSquared x ≤ x ^ 2 := by
  by_cases hx : 0 ≤ x
  · simp [positiveSquared, max_eq_right hx]
  · simp [positiveSquared, max_eq_left (le_of_not_ge hx), sq_nonneg]

theorem positiveSquared_add_neg (x : ℝ) : positiveSquared x + positiveSquared (-x) = x ^ 2 := by
  by_cases hx : 0 ≤ x
  · simp [positiveSquared, max_eq_right hx, max_eq_left (neg_nonpos.mpr hx)]
  · have hn : x ≤ 0 := le_of_not_ge hx
    simp [positiveSquared, max_eq_left hn, max_eq_right (neg_nonneg.mpr hn)]

theorem gaussian_sq_memLp_four : MemLp (fun x : ℝ => x ^ 2) 4 (gaussianReal 0 1) := by
  let _ : ENNReal.HolderTriple 8 8 4 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)).mp
    norm_num [ENNReal.toReal_add]⟩
  have h : MemLp (fun x : ℝ => x) 8 (gaussianReal 0 1) :=
    IsGaussian.memLp_id (gaussianReal 0 1) 8 (by norm_num)
  simpa only [pow_two] using h.fun_mul h

theorem gaussian_positiveSquared_memLp_four : MemLp positiveSquared 4 (gaussianReal 0 1) := by
  apply gaussian_sq_memLp_four.of_le continuous_positiveSquared.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  simp only [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ positiveSquared x by unfold positiveSquared; positivity),
    abs_of_nonneg (sq_nonneg x)]
  exact positiveSquared_le_sq x

theorem integral_gaussian_sq : (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1) = 1 := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  change Var[id; gaussianReal 0 1] = (1 : ℝ) at h
  rw [variance_eq_integral measurable_id.aemeasurable] at h
  simp only [id_eq, integral_id_gaussianReal, sub_zero] at h
  exact h

theorem integral_gaussian_positiveSquared :
    (∫ x, positiveSquared x ∂gaussianReal 0 1) = (1 / 2 : ℝ) := by
  have hp := gaussian_positiveSquared_memLp_four.integrable (by norm_num)
  have hn : HasLaw (fun x : ℝ => -x) (gaussianReal 0 1) (gaussianReal 0 1) :=
    ⟨measurable_neg.aemeasurable, by simpa using (gaussianReal_map_neg (μ := 0) (v := 1))⟩
  have hi := hn.integral_comp hp.aestronglyMeasurable
  have hneg := hn.integrable_comp hp
  have he : (fun x => positiveSquared x + positiveSquared (-x)) = (fun x => x ^ 2) := by
    funext x
    exact positiveSquared_add_neg x
  have hadd := integral_add hp hneg
  simp only [Function.comp_def] at hi hadd
  rw [he, integral_gaussian_sq, hi] at hadd
  linarith

theorem ae_gaussian_average_sq_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ → Type*} [∀ k, Fintype (n k)]
    (G : ∀ k, Ω → (n k → ℝ)) (hG : ∀ k, HasLaw (G k) (gaussianVector (n k)) μ)
    (δ : ℝ) (hδ : 0 < δ)
    (hdim : ∀ k : ℕ, δ * ((k : ℝ) + 1) ≤ (Fintype.card (n k) : ℝ)) :
    ∀ᵐ ω ∂μ, Tendsto (fun k => (∑ i, G k ω i ^ 2) / (Fintype.card (n k) : ℝ))
      atTop (nhds 1) := by
  simpa only [integral_gaussian_sq] using ae_product_law_average_tendsto
    (gaussianReal 0 1) (fun x : ℝ => x ^ 2) (measurable_id.pow_const 2)
    gaussian_sq_memLp_four G hG δ hδ hdim

theorem ae_gaussian_average_positiveSquared_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ → Type*} [∀ k, Fintype (n k)]
    (G : ∀ k, Ω → (n k → ℝ)) (hG : ∀ k, HasLaw (G k) (gaussianVector (n k)) μ)
    (δ : ℝ) (hδ : 0 < δ)
    (hdim : ∀ k : ℕ, δ * ((k : ℝ) + 1) ≤ (Fintype.card (n k) : ℝ)) :
    ∀ᵐ ω ∂μ, Tendsto (fun k => (∑ i, positiveSquared (G k ω i)) /
      (Fintype.card (n k) : ℝ)) atTop (nhds (1 / 2 : ℝ)) := by
  simpa only [integral_gaussian_positiveSquared] using ae_product_law_average_tendsto
    (gaussianReal 0 1) positiveSquared continuous_positiveSquared.measurable
    gaussian_positiveSquared_memLp_four G hG δ hδ hdim

noncomputable def positiveEnergyFraction {n : Type*} [Fintype n] (v : n → ℝ) : ℝ :=
  (∑ i, positiveSquared (v i)) / (∑ i, v i ^ 2)

theorem ae_gaussian_positiveEnergyFraction_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ → Type*} [∀ k, Fintype (n k)]
    (G : ∀ k, Ω → (n k → ℝ)) (hG : ∀ k, HasLaw (G k) (gaussianVector (n k)) μ)
    (δ : ℝ) (hδ : 0 < δ)
    (hdim : ∀ k : ℕ, δ * ((k : ℝ) + 1) ≤ (Fintype.card (n k) : ℝ)) :
    ∀ᵐ ω ∂μ, Tendsto (fun k => positiveEnergyFraction (G k ω))
      atTop (nhds (1 / 2 : ℝ)) := by
  have hp := ae_gaussian_average_positiveSquared_tendsto μ G hG δ hδ hdim
  have hs := ae_gaussian_average_sq_tendsto μ G hG δ hδ hdim
  filter_upwards [hp, hs] with ω hωp hωs
  have h := hωp.div hωs (by norm_num : (1 : ℝ) ≠ 0)
  change Tendsto (fun k =>
    ((∑ i, positiveSquared (G k ω i)) / (Fintype.card (n k) : ℝ)) /
      ((∑ i, G k ω i ^ 2) / (Fintype.card (n k) : ℝ))) atTop (nhds ((1 / 2 : ℝ) / 1)) at h
  have he (k : ℕ) : ((∑ i, positiveSquared (G k ω i)) / (Fintype.card (n k) : ℝ)) /
      ((∑ i, G k ω i ^ 2) / (Fintype.card (n k) : ℝ)) = positiveEnergyFraction (G k ω) := by
    have hN : (0 : ℝ) < Fintype.card (n k) :=
      (mul_pos hδ (by positivity)).trans_le (hdim k)
    exact div_div_div_cancel_right₀ hN.ne' _ _
  simpa only [he, div_one] using h

theorem measurable_positiveEnergyFraction {n : Type*} [Fintype n] :
    Measurable (positiveEnergyFraction (n := n)) := by
  classical
  unfold positiveEnergyFraction positiveSquared
  fun_prop

theorem positiveSquared_mul_nonneg (a x : ℝ) (ha : 0 ≤ a) :
    positiveSquared (a * x) = a ^ 2 * positiveSquared x := by
  by_cases hx : 0 ≤ x
  · simp [positiveSquared, max_eq_right hx, max_eq_right (mul_nonneg ha hx), mul_pow]
  · have hn : x ≤ 0 := le_of_not_ge hx
    simp [positiveSquared, max_eq_left hn, max_eq_left (mul_nonpos_of_nonneg_of_nonpos ha hn)]

theorem positiveEnergyFraction_smul {n : Type*} [Fintype n] (a : ℝ) (ha : 0 < a) (v : n → ℝ) :
    positiveEnergyFraction (a • v) = positiveEnergyFraction v := by
  simp only [positiveEnergyFraction, Pi.smul_apply, smul_eq_mul,
    positiveSquared_mul_nonneg a _ ha.le, mul_pow, ← Finset.mul_sum]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 ha.ne')

theorem positiveEnergyFraction_direction {n : Type*} [Fintype n] (v : n → ℝ) :
    positiveEnergyFraction (direction v) = positiveEnergyFraction v := by
  by_cases hv : v = 0
  · simp [hv, direction_zero]
  · have hn : 0 < ‖WithLp.toLp 2 v‖ := norm_pos_iff.mpr (by simpa using hv)
    exact positiveEnergyFraction_smul _ (inv_pos.mpr hn) v

end FreeProbability.Orthogonal

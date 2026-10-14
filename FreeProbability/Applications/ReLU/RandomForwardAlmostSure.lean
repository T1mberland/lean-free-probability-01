import FreeProbability.Applications.ReLU.RandomForwardModel
import FreeProbability.RandomMatrix.DimensionSummability
import FreeProbability.RandomMatrix.AlmostSureFromTails

/-! # Almost-sure forward limits for independent random initial inputs -/

namespace FreeProbability.ReLU

open Matrix MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {n : ℕ → Type*} [∀ k, Fintype (n k)] [∀ k, DecidableEq (n k)]
    {Θ : ℕ → Type*} [∀ k, MeasurableSpace (Θ k)]
    (ν : ∀ k, Measure (Θ k)) [∀ k, IsProbabilityMeasure (ν k)]
    (X : ∀ k, Θ k → (n k → ℝ)) (hX : ∀ k, Measurable (X k))
    (hx : ∀ k, ∀ᵐ θ ∂ν k, X k θ ≠ 0) (L : ℕ)
    (σ : ℕ → Fin L → ℝ) (hσ : ∀ k i, 0 < σ k i)
    (Y : ∀ k, Ω → Θ k × Weights (n k) L)
    (hY : ∀ k, HasLaw (Y k) ((ν k).prod (weightLaw (n k) L)) μ)
    (δ : ℝ) (hδ : 0 < δ)
    (hdim : ∀ k : ℕ, δ * ((k : ℝ) + 1) ≤ (Fintype.card (n k) : ℝ))

include hX hx hσ hY hδ hdim in
/-- A fixed-depth network is eventually alive almost surely, despite a positive
extinction probability at every finite width. -/
theorem ae_randomForwardState_eventually_ne_zero :
    ∀ᵐ ω ∂μ, ∀ᶠ k in atTop, randomForwardState (X k) L (σ k) (Y k ω) ≠ 0 := by
  have ht : (∑' k, μ {ω | randomForwardState (X k) L (σ k) (Y k ω) = 0}) ≠ ∞ := by
    apply tsum_ne_top_of_geometric_quadratic_bound _ (fun k => Fintype.card (n k))
      (1 / 2) δ L 0 (by norm_num) (by norm_num) hδ hdim
    intro k
    simp only [zero_div, ENNReal.ofReal_zero, add_zero]
    have hm : MeasurableSet {V : Θ k × Weights (n k) L | randomForwardState (X k) L (σ k) V = 0} :=
      (measurable_randomForwardState (X k) (hX k) L (σ k)) (measurableSet_singleton 0)
    rw [(hY k).measure_eq hm]
    exact randomForwardState_zero_probability_le (ν k) (X k) (hX k) (hx k) L (σ k) (hσ k)
  exact ae_eventually_notMem ht

omit L σ hσ Y hY in
include hX hx hδ hdim in
/-- Surviving energy has the one-half limit for the actual finite-depth model.
No independence between widths is assumed. -/
theorem ae_randomForwardPreactivation_energy_tendsto (L : ℕ)
    (σ : ℕ → Fin (L + 1) → ℝ) (hσ : ∀ k i, 0 < σ k i)
    (Y : ∀ k, Ω → Θ k × Weights (n k) (L + 1))
    (hY : ∀ k, HasLaw (Y k) ((ν k).prod (weightLaw (n k) (L + 1))) μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun k => gateEnergyFraction
      (randomForwardPreactivation (X k) L (σ k) (Y k ω))) atTop (nhds (1 / 2 : ℝ)) := by
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun k => Orthogonal.positiveEnergyFraction
      (randomForwardPreactivation (X k) L (σ k) (Y k ω)) - 1 / 2) atTop (nhds 0) := by
    apply ae_tendsto_zero_of_summable_deviations
    intro ε hε
    let t := Orthogonal.energyDeviationThreshold ε
    have ht : 0 < t := Orthogonal.energyDeviationThreshold_pos hε
    apply tsum_ne_top_of_geometric_quadratic_bound _ (fun k => Fintype.card (n k))
      (1 / 2) δ L (Orthogonal.energyFourthMomentBound / t ^ 4)
      (by norm_num) (by norm_num) hδ hdim
    intro k
    have hR := Orthogonal.measurable_positiveEnergyFraction.comp
      (measurable_randomForwardPreactivation (X k) (hX k) L (σ k))
    have hm : MeasurableSet {V : Θ k × Weights (n k) (L + 1) | ε ≤
        |Orthogonal.positiveEnergyFraction (randomForwardPreactivation (X k) L (σ k) V) - 1 / 2|} :=
      measurableSet_le measurable_const ((show Measurable (fun a : ℝ => |a|) from
        continuous_id.abs.measurable).comp (hR.sub measurable_const))
    rw [(hY k).measure_eq hm]
    have h := randomForwardPreactivation_energy_deviation_le (ν k) (X k) (hX k) (hx k) L (σ k) (hσ k) ε hε
    simpa only [div_div, mul_comm (t ^ 4)] using h
  filter_upwards [hlim] with ω hω
  have hc : Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (nhds (1 / 2 : ℝ)) := tendsto_const_nhds
  have h := hω.add hc
  simpa only [sub_add_cancel, zero_add, gateEnergyFraction_eq_positiveEnergyFraction] using h

omit L σ hσ Y hY in
include hX hx hδ hdim in
theorem ae_randomForwardPreactivation_gateDensity_tendsto (L : ℕ)
    (σ : ℕ → Fin (L + 1) → ℝ) (hσ : ∀ k i, 0 < σ k i)
    (Y : ∀ k, Ω → Θ k × Weights (n k) (L + 1))
    (hY : ∀ k, HasLaw (Y k) ((ν k).prod (weightLaw (n k) (L + 1))) μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun k =>
      (Orthogonal.gateRank (randomForwardPreactivation (X k) L (σ k) (Y k ω)) : ℝ) /
        (Fintype.card (n k) : ℝ)) atTop (nhds (1 / 2 : ℝ)) := by
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun k =>
      (Orthogonal.gateRank (randomForwardPreactivation (X k) L (σ k) (Y k ω)) : ℝ) /
        (Fintype.card (n k) : ℝ) - 1 / 2) atTop (nhds 0) := by
    apply ae_tendsto_zero_of_summable_deviations
    intro ε hε
    have ha : -2 * ε ^ 2 < 0 := mul_neg_of_neg_of_pos (by norm_num) (sq_pos_of_pos hε)
    apply tsum_ne_top_of_geometric_exponential_bound _ (fun k => Fintype.card (n k))
      (1 / 2) (-2 * ε ^ 2) δ L 2 (by norm_num) (by norm_num) ha hδ hdim
    intro k
    have hB : MeasurableSet {j : ℕ | ε ≤ |(j : ℝ) / (Fintype.card (n k) : ℝ) - 1 / 2|} := .of_discrete
    have hS : MeasurableSet {V : Θ k × Weights (n k) (L + 1) | ε ≤
        |(Orthogonal.gateRank (randomForwardPreactivation (X k) L (σ k) V) : ℝ) /
          (Fintype.card (n k) : ℝ) - 1 / 2|} :=
      (Orthogonal.measurable_gateRank.comp (measurable_randomForwardPreactivation (X k) (hX k) L (σ k))) hB
    rw [(hY k).measure_eq hS]
    have h := randomForwardPreactivation_gateRank_deviation_le (ν k) (X k) (hX k) (hx k) L (σ k) (hσ k) ε hε.le
    rw [show -2 * (Fintype.card (n k) : ℝ) * ε ^ 2 =
      (-2 * ε ^ 2) * (Fintype.card (n k) : ℝ) by ring] at h
    exact h
  filter_upwards [hlim] with ω hω
  have hc : Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (nhds (1 / 2 : ℝ)) := tendsto_const_nhds
  have h := hω.add hc
  simpa only [sub_add_cancel, zero_add] using h

omit L σ hσ Y hY in
include hX hx hδ hdim in
theorem ae_randomForwardPreactivation_gateAmplitude_tendsto (L : ℕ)
    (σ : ℕ → Fin (L + 1) → ℝ) (hσ : ∀ k i, 0 < σ k i)
    (Y : ∀ k, Ω → Θ k × Weights (n k) (L + 1))
    (hY : ∀ k, HasLaw (Y k) ((ν k).prod (weightLaw (n k) (L + 1))) μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun k => gateAmplitude
      (randomForwardPreactivation (X k) L (σ k) (Y k ω))) atTop (nhds (Real.sqrt (1 / 2))) := by
  filter_upwards [ae_randomForwardPreactivation_energy_tendsto μ ν X hX hx δ hδ hdim L σ hσ Y hY] with ω hω
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hω
  simpa only [Function.comp_def, sqrt_gateEnergyFraction] using h

omit L σ hσ Y hY in
include hX hx hδ hdim in
theorem ae_randomForwardPreactivation_gateRank_eventually_nontrivial (L : ℕ)
    (σ : ℕ → Fin (L + 1) → ℝ) (hσ : ∀ k i, 0 < σ k i)
    (Y : ∀ k, Ω → Θ k × Weights (n k) (L + 1))
    (hY : ∀ k, HasLaw (Y k) ((ν k).prod (weightLaw (n k) (L + 1))) μ) :
    ∀ᵐ ω ∂μ, ∀ᶠ k in atTop,
      0 < Orthogonal.gateRank (randomForwardPreactivation (X k) L (σ k) (Y k ω)) ∧
        Orthogonal.gateRank (randomForwardPreactivation (X k) L (σ k) (Y k ω)) < Fintype.card (n k) := by
  filter_upwards [ae_randomForwardPreactivation_gateDensity_tendsto μ ν X hX hx δ hδ hdim L σ hσ Y hY] with ω hω
  have hev := hω.eventually (Ioo_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1))
  filter_upwards [hev] with k hk
  have hd : (0 : ℝ) < Fintype.card (n k) := (mul_pos hδ (by positivity)).trans_le (hdim k)
  have hpos : (0 : ℝ) < Orthogonal.gateRank (randomForwardPreactivation (X k) L (σ k) (Y k ω)) :=
    (div_pos_iff_of_pos_right hd).mp hk.1
  have hlt : (Orthogonal.gateRank (randomForwardPreactivation (X k) L (σ k) (Y k ω)) : ℝ) <
      Fintype.card (n k) := (div_lt_one hd).mp hk.2
  constructor
  · exact_mod_cast hpos
  · exact_mod_cast hlt

end FreeProbability.ReLU

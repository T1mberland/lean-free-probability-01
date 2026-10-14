import FreeProbability.Applications.ReLU.ForwardModel
import FreeProbability.RandomMatrix.DimensionSummability
import FreeProbability.RandomMatrix.AlmostSureFromTails

/-! # Almost-sure finite-depth forward limits with arbitrary width coupling -/

namespace FreeProbability.ReLU

open Matrix MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {n : ℕ → Type*} [∀ k, Fintype (n k)] [∀ k, DecidableEq (n k)]
    (x : ∀ k, n k → ℝ) (hx : ∀ k, x k ≠ 0) (L : ℕ)
    (σ : ℕ → Fin L → ℝ) (hσ : ∀ k i, 0 < σ k i)
    (W : ∀ k, Ω → Weights (n k) L) (hW : ∀ k, HasLaw (W k) (weightLaw (n k) L) μ)
    (δ : ℝ) (hδ : 0 < δ)
    (hdim : ∀ k : ℕ, δ * ((k : ℝ) + 1) ≤ (Fintype.card (n k) : ℝ))

include hx hσ hW hδ hdim in
/-- A fixed-depth network is eventually alive almost surely, despite a positive
extinction probability at every finite width. -/
theorem ae_forwardState_eventually_ne_zero :
    ∀ᵐ ω ∂μ, ∀ᶠ k in atTop, forwardState (x k) L (σ k) (W k ω) ≠ 0 := by
  have ht : (∑' k, μ {ω | forwardState (x k) L (σ k) (W k ω) = 0}) ≠ ∞ := by
    apply tsum_ne_top_of_geometric_quadratic_bound _ (fun k => Fintype.card (n k))
      (1 / 2) δ L 0 (by norm_num) (by norm_num) hδ hdim
    intro k
    simp only [zero_div, ENNReal.ofReal_zero, add_zero]
    have hm : MeasurableSet {V : Weights (n k) L | forwardState (x k) L (σ k) V = 0} :=
      (measurable_forwardState (x k) L (σ k)) (measurableSet_singleton 0)
    rw [(hW k).measure_eq hm]
    exact forwardState_zero_probability_le (x k) (hx k) L (σ k) (hσ k)
  exact ae_eventually_notMem ht

omit L σ hσ W hW in
include hx hδ hdim in
/-- Surviving energy has the one-half limit for the actual finite-depth model.
No independence between widths is assumed. -/
theorem ae_forwardPreactivation_energy_tendsto (L : ℕ)
    (σ : ℕ → Fin (L + 1) → ℝ) (hσ : ∀ k i, 0 < σ k i)
    (W : ∀ k, Ω → Weights (n k) (L + 1))
    (hW : ∀ k, HasLaw (W k) (weightLaw (n k) (L + 1)) μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun k => gateEnergyFraction
      (forwardPreactivation (x k) L (σ k) (W k ω))) atTop (nhds (1 / 2 : ℝ)) := by
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun k => Orthogonal.positiveEnergyFraction
      (forwardPreactivation (x k) L (σ k) (W k ω)) - 1 / 2) atTop (nhds 0) := by
    apply ae_tendsto_zero_of_summable_deviations
    intro ε hε
    let t := Orthogonal.energyDeviationThreshold ε
    have ht : 0 < t := Orthogonal.energyDeviationThreshold_pos hε
    apply tsum_ne_top_of_geometric_quadratic_bound _ (fun k => Fintype.card (n k))
      (1 / 2) δ L (Orthogonal.energyFourthMomentBound / t ^ 4)
      (by norm_num) (by norm_num) hδ hdim
    intro k
    have hR := Orthogonal.measurable_positiveEnergyFraction.comp
      (measurable_forwardPreactivation (x k) L (σ k))
    have hm : MeasurableSet {V : Weights (n k) (L + 1) | ε ≤
        |Orthogonal.positiveEnergyFraction (forwardPreactivation (x k) L (σ k) V) - 1 / 2|} :=
      measurableSet_le measurable_const ((show Measurable (fun a : ℝ => |a|) from
        continuous_id.abs.measurable).comp (hR.sub measurable_const))
    rw [(hW k).measure_eq hm]
    have h := forwardPreactivation_energy_deviation_le (x k) (hx k) L (σ k) (hσ k) ε hε
    simpa only [div_div, mul_comm (t ^ 4)] using h
  filter_upwards [hlim] with ω hω
  have hc : Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (nhds (1 / 2 : ℝ)) := tendsto_const_nhds
  have h := hω.add hc
  simpa only [sub_add_cancel, zero_add, gateEnergyFraction_eq_positiveEnergyFraction] using h

omit L σ hσ W hW in
include hx hδ hdim in
theorem ae_forwardPreactivation_gateDensity_tendsto (L : ℕ)
    (σ : ℕ → Fin (L + 1) → ℝ) (hσ : ∀ k i, 0 < σ k i)
    (W : ∀ k, Ω → Weights (n k) (L + 1))
    (hW : ∀ k, HasLaw (W k) (weightLaw (n k) (L + 1)) μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun k =>
      (Orthogonal.gateRank (forwardPreactivation (x k) L (σ k) (W k ω)) : ℝ) /
        (Fintype.card (n k) : ℝ)) atTop (nhds (1 / 2 : ℝ)) := by
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun k =>
      (Orthogonal.gateRank (forwardPreactivation (x k) L (σ k) (W k ω)) : ℝ) /
        (Fintype.card (n k) : ℝ) - 1 / 2) atTop (nhds 0) := by
    apply ae_tendsto_zero_of_summable_deviations
    intro ε hε
    have ha : -2 * ε ^ 2 < 0 := mul_neg_of_neg_of_pos (by norm_num) (sq_pos_of_pos hε)
    apply tsum_ne_top_of_geometric_exponential_bound _ (fun k => Fintype.card (n k))
      (1 / 2) (-2 * ε ^ 2) δ L 2 (by norm_num) (by norm_num) ha hδ hdim
    intro k
    have hB : MeasurableSet {j : ℕ | ε ≤ |(j : ℝ) / (Fintype.card (n k) : ℝ) - 1 / 2|} := .of_discrete
    have hS : MeasurableSet {V : Weights (n k) (L + 1) | ε ≤
        |(Orthogonal.gateRank (forwardPreactivation (x k) L (σ k) V) : ℝ) /
          (Fintype.card (n k) : ℝ) - 1 / 2|} :=
      (Orthogonal.measurable_gateRank.comp (measurable_forwardPreactivation (x k) L (σ k))) hB
    rw [(hW k).measure_eq hS]
    have h := forwardPreactivation_gateRank_deviation_le (x k) (hx k) L (σ k) (hσ k) ε hε.le
    rw [show -2 * (Fintype.card (n k) : ℝ) * ε ^ 2 =
      (-2 * ε ^ 2) * (Fintype.card (n k) : ℝ) by ring] at h
    exact h
  filter_upwards [hlim] with ω hω
  have hc : Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (nhds (1 / 2 : ℝ)) := tendsto_const_nhds
  have h := hω.add hc
  simpa only [sub_add_cancel, zero_add] using h

omit L σ hσ W hW in
include hx hδ hdim in
theorem ae_forwardPreactivation_gateAmplitude_tendsto (L : ℕ)
    (σ : ℕ → Fin (L + 1) → ℝ) (hσ : ∀ k i, 0 < σ k i)
    (W : ∀ k, Ω → Weights (n k) (L + 1))
    (hW : ∀ k, HasLaw (W k) (weightLaw (n k) (L + 1)) μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun k => gateAmplitude
      (forwardPreactivation (x k) L (σ k) (W k ω))) atTop (nhds (Real.sqrt (1 / 2))) := by
  filter_upwards [ae_forwardPreactivation_energy_tendsto μ x hx δ hδ hdim L σ hσ W hW] with ω hω
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hω
  simpa only [Function.comp_def, sqrt_gateEnergyFraction] using h

omit L σ hσ W hW in
include hx hδ hdim in
theorem ae_forwardPreactivation_gateRank_eventually_nontrivial (L : ℕ)
    (σ : ℕ → Fin (L + 1) → ℝ) (hσ : ∀ k i, 0 < σ k i)
    (W : ∀ k, Ω → Weights (n k) (L + 1))
    (hW : ∀ k, HasLaw (W k) (weightLaw (n k) (L + 1)) μ) :
    ∀ᵐ ω ∂μ, ∀ᶠ k in atTop,
      0 < Orthogonal.gateRank (forwardPreactivation (x k) L (σ k) (W k ω)) ∧
        Orthogonal.gateRank (forwardPreactivation (x k) L (σ k) (W k ω)) < Fintype.card (n k) := by
  filter_upwards [ae_forwardPreactivation_gateDensity_tendsto μ x hx δ hδ hdim L σ hσ W hW] with ω hω
  have hev := hω.eventually (Ioo_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1))
  filter_upwards [hev] with k hk
  have hd : (0 : ℝ) < Fintype.card (n k) := (mul_pos hδ (by positivity)).trans_le (hdim k)
  have hpos : (0 : ℝ) < Orthogonal.gateRank (forwardPreactivation (x k) L (σ k) (W k ω)) :=
    (div_pos_iff_of_pos_right hd).mp hk.1
  have hlt : (Orthogonal.gateRank (forwardPreactivation (x k) L (σ k) (W k ω)) : ℝ) <
      Fintype.card (n k) := (div_lt_one hd).mp hk.2
  constructor
  · exact_mod_cast hpos
  · exact_mod_cast hlt

end FreeProbability.ReLU

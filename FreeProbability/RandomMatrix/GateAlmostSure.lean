import FreeProbability.RandomMatrix.GateConcentration
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # Almost-sure gate-density limits under arbitrary cross-width couplings -/

namespace FreeProbability.Orthogonal

open Matrix MeasureTheory ProbabilityTheory Filter Real
open scoped ENNReal

/-- Half-binomial densities converge almost surely when dimensions grow at least
linearly. Only each marginal law is required; couplings between widths are arbitrary. -/
theorem ae_binomial_half_density_tendsto {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (d : ℕ → ℕ) (K : ℕ → Ω → ℕ)
    (hK : ∀ k, HasLaw (K k) (binomial (d k) halfProbability) μ)
    (δ : ℝ) (hδ : 0 < δ) (hdim : ∀ k : ℕ, δ * ((k : ℝ) + 1) ≤ (d k : ℝ)) :
    ∀ᵐ ω ∂μ, Tendsto (fun k => (K k ω : ℝ) / (d k : ℝ)) atTop (nhds (1 / 2 : ℝ)) := by
  let _ : IsProbabilityMeasure μ := (hK 0).isProbabilityMeasure
  have hz : ∀ᵐ ω ∂μ, Tendsto (fun k => (K k ω : ℝ) / (d k : ℝ) - 1 / 2) atTop (nhds 0) := by
    apply ae_tendsto_zero_of_summable_deviations
    intro ε hε
    let b := fun k : ℕ => 2 * exp (-2 * δ * ((k : ℝ) + 1) * ε ^ 2)
    have ht (k : ℕ) : μ {ω | ε ≤ |(K k ω : ℝ) / (d k : ℝ) - 1 / 2|} ≤
        ENNReal.ofReal (b k) := by
      have hd : (0 : ℝ) < d k := (mul_pos hδ (by positivity)).trans_le (hdim k)
      have hdN : 0 < d k := by exact_mod_cast hd
      have hm : MeasurableSet {j : ℕ | ε ≤ |(j : ℝ) / (d k : ℝ) - 1 / 2|} := .of_discrete
      have hl := (hK k).measureReal_eq hm
      have hright := binomial_half_deviation_le (d k) hdN ε hε.le
      have hg : -2 * (d k : ℝ) * ε ^ 2 ≤ -2 * δ * ((k : ℝ) + 1) * ε ^ 2 := by
        have h := mul_le_mul_of_nonneg_right (hdim k) (sq_nonneg ε)
        nlinarith
      have hr : μ.real {ω | ε ≤ |(K k ω : ℝ) / (d k : ℝ) - 1 / 2|} ≤ b k := by
        rw [hl]
        exact hright.trans (mul_le_mul_of_nonneg_left (exp_le_exp.mpr hg) (by norm_num))
      have h := ENNReal.ofReal_le_ofReal hr
      rw [ofReal_measureReal (μ := μ)] at h
      exact h
    have ha : -2 * δ * ε ^ 2 < 0 := mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (by norm_num) hδ) (sq_pos_of_pos hε)
    have hs := Real.summable_exp_nat_mul_iff.mpr ha
    have hshift : Summable (fun k : ℕ => exp (((k : ℝ) + 1) * (-2 * δ * ε ^ 2))) := by
      simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hs
    have hb : Summable b := (hshift.mul_left 2).congr (fun k => by
      change 2 * exp (((k : ℝ) + 1) * (-2 * δ * ε ^ 2)) =
        2 * exp (-2 * δ * ((k : ℝ) + 1) * ε ^ 2)
      rw [show ((k : ℝ) + 1) * (-2 * δ * ε ^ 2) =
        -2 * δ * ((k : ℝ) + 1) * ε ^ 2 by ring])
    exact (lt_of_le_of_lt (ENNReal.tsum_le_tsum ht) hb.tsum_ofReal_lt_top).ne
  filter_upwards [hz] with ω hω
  have hc : Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (nhds (1 / 2 : ℝ)) := tendsto_const_nhds
  have h := hω.add hc
  simpa only [sub_add_cancel, zero_add] using h

/-- Concrete Haar weights acting on fixed nonzero inputs give the same almost-sure
limit, without independence of the weights between widths. -/
theorem ae_haar_gateRank_density_tendsto {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {n : ℕ → Type*} [∀ k, Fintype (n k)] [∀ k, DecidableEq (n k)]
    (x : ∀ k, n k → ℝ) (hx : ∀ k, x k ≠ 0) (U : ∀ k, Ω → Group (n k))
    (hU : ∀ k, HasLaw (U k) (haar (n k)) μ)
    (δ : ℝ) (hδ : 0 < δ) (hdim : ∀ k : ℕ, δ * ((k : ℝ) + 1) ≤ (Fintype.card (n k) : ℝ)) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun k => (gateRank ((U k ω : Matrix (n k) (n k) ℝ) *ᵥ x k) : ℝ) /
        (Fintype.card (n k) : ℝ)) atTop (nhds (1 / 2 : ℝ)) := by
  apply ae_binomial_half_density_tendsto μ (fun k => Fintype.card (n k)) _ _ δ hδ hdim
  intro k
  exact (gateRank_haar_hasLaw (x k) (hx k)).fun_comp (hU k)

theorem ae_binomial_half_eventually_nontrivial {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (d : ℕ → ℕ) (K : ℕ → Ω → ℕ)
    (hK : ∀ k, HasLaw (K k) (binomial (d k) halfProbability) μ)
    (δ : ℝ) (hδ : 0 < δ) (hdim : ∀ k : ℕ, δ * ((k : ℝ) + 1) ≤ (d k : ℝ)) :
    ∀ᵐ ω ∂μ, ∀ᶠ k in atTop, 0 < K k ω ∧ K k ω < d k := by
  have hlim := ae_binomial_half_density_tendsto μ d K hK δ hδ hdim
  filter_upwards [hlim] with ω hω
  have hev : ∀ᶠ k in atTop, (K k ω : ℝ) / (d k : ℝ) ∈ Set.Ioo (0 : ℝ) 1 :=
    hω.eventually (Ioo_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1))
  filter_upwards [hev] with k hk
  have hd : (0 : ℝ) < d k := (mul_pos hδ (by positivity)).trans_le (hdim k)
  have hKpos : (0 : ℝ) < K k ω := (div_pos_iff_of_pos_right hd).mp hk.1
  have hKlt : (K k ω : ℝ) < d k := (div_lt_one hd).mp hk.2
  constructor
  · exact_mod_cast hKpos
  · exact_mod_cast hKlt

/-- Eventually both active and inactive coordinates occur for Haar weights on
nonzero inputs, under arbitrary coupling between the growing widths. -/
theorem ae_haar_gateRank_eventually_nontrivial {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {n : ℕ → Type*} [∀ k, Fintype (n k)] [∀ k, DecidableEq (n k)]
    (x : ∀ k, n k → ℝ) (hx : ∀ k, x k ≠ 0) (U : ∀ k, Ω → Group (n k))
    (hU : ∀ k, HasLaw (U k) (haar (n k)) μ)
    (δ : ℝ) (hδ : 0 < δ) (hdim : ∀ k : ℕ, δ * ((k : ℝ) + 1) ≤ (Fintype.card (n k) : ℝ)) :
    ∀ᵐ ω ∂μ, ∀ᶠ k in atTop,
      0 < gateRank ((U k ω : Matrix (n k) (n k) ℝ) *ᵥ x k) ∧
        gateRank ((U k ω : Matrix (n k) (n k) ℝ) *ᵥ x k) < Fintype.card (n k) := by
  apply ae_binomial_half_eventually_nontrivial μ (fun k => Fintype.card (n k)) _ _ δ hδ hdim
  intro k
  exact (gateRank_haar_hasLaw (x k) (hx k)).fun_comp (hU k)

end FreeProbability.Orthogonal

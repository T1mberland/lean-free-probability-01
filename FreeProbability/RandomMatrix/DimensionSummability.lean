import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Summable geometric and quadratic tails for linearly growing dimensions -/

namespace FreeProbability

open Real
open scoped ENNReal

theorem summable_pow_of_dimension_growth (d : ℕ → ℕ) (p δ : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hδ : 0 < δ)
    (hdim : ∀ k : ℕ, δ * ((k : ℝ) + 1) ≤ (d k : ℝ)) :
    Summable (fun k => p ^ d k) := by
  have hl : log p < 0 := log_neg hp hp1
  have ha : δ * log p < 0 := mul_neg_of_pos_of_neg hδ hl
  have hs := Real.summable_exp_nat_mul_iff.mpr ha
  have hshift : Summable (fun k : ℕ => exp (((k : ℝ) + 1) * (δ * log p))) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hs
  apply Summable.of_nonneg_of_le (fun k => (pow_pos hp _).le) _ hshift
  intro k
  rw [← Real.rpow_natCast p (d k), Real.rpow_def_of_pos hp]
  apply exp_le_exp.mpr
  calc
    log p * (d k : ℝ) ≤ log p * (δ * ((k : ℝ) + 1)) :=
      mul_le_mul_of_nonpos_left (hdim k) hl.le
    _ = _ := by ring

theorem summable_inv_sq_of_dimension_growth (d : ℕ → ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hdim : ∀ k : ℕ, δ * ((k : ℝ) + 1) ≤ (d k : ℝ)) :
    Summable (fun k => 1 / (d k : ℝ) ^ 2) := by
  have hp := (Real.summable_one_div_nat_pow (p := 2)).mpr (by decide)
  have hs : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hp
  apply Summable.of_nonneg_of_le (fun k => by positivity) _ (hs.mul_left (1 / δ ^ 2))
  intro k
  have hk : 0 < (k : ℝ) + 1 := by positivity
  have hsq : δ ^ 2 * ((k : ℝ) + 1) ^ 2 ≤ (d k : ℝ) ^ 2 := by
    simpa [mul_pow] using pow_le_pow_left₀ (mul_pos hδ hk).le (hdim k) 2
  calc
    _ ≤ 1 / (δ ^ 2 * ((k : ℝ) + 1) ^ 2) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hsq
    _ = _ := by field_simp [hδ.ne', hk.ne']

theorem tsum_ne_top_of_geometric_quadratic_bound (b : ℕ → ℝ≥0∞) (d : ℕ → ℕ)
    (p δ A C : ℝ) (hp : 0 < p) (hp1 : p < 1) (hδ : 0 < δ)
    (hdim : ∀ k : ℕ, δ * ((k : ℝ) + 1) ≤ (d k : ℝ))
    (h : ∀ k, b k ≤ ENNReal.ofReal (A * p ^ d k) + ENNReal.ofReal (C / (d k : ℝ) ^ 2)) :
    (∑' k, b k) ≠ ∞ := by
  have hs := (summable_pow_of_dimension_growth d p δ hp hp1 hδ hdim).mul_left A
  have hq : Summable (fun k => C / (d k : ℝ) ^ 2) := by
    simpa only [mul_one_div] using (summable_inv_sq_of_dimension_growth d δ hδ hdim).mul_left C
  have hsum := ENNReal.tsum_le_tsum h
  rw [ENNReal.tsum_add] at hsum
  exact (lt_of_le_of_lt hsum (ENNReal.add_lt_top.mpr
    ⟨hs.tsum_ofReal_lt_top, hq.tsum_ofReal_lt_top⟩)).ne

theorem tsum_ne_top_of_geometric_exponential_bound (b : ℕ → ℝ≥0∞) (d : ℕ → ℕ)
    (p a δ A B : ℝ) (hp : 0 < p) (hp1 : p < 1) (ha : a < 0) (hδ : 0 < δ)
    (hdim : ∀ k : ℕ, δ * ((k : ℝ) + 1) ≤ (d k : ℝ))
    (h : ∀ k, b k ≤ ENNReal.ofReal (A * p ^ d k) + ENNReal.ofReal (B * exp (a * (d k : ℝ)))) :
    (∑' k, b k) ≠ ∞ := by
  have hs := (summable_pow_of_dimension_growth d p δ hp hp1 hδ hdim).mul_left A
  have hq : Summable (fun k => B * exp (a * (d k : ℝ))) := by
    have hg := (summable_pow_of_dimension_growth d (exp a) δ
      (exp_pos a) (exp_lt_one_iff.mpr ha) hδ hdim).mul_left B
    simpa only [mul_comm a, exp_nat_mul] using hg
  have hsum := ENNReal.tsum_le_tsum h
  rw [ENNReal.tsum_add] at hsum
  exact (lt_of_le_of_lt hsum (ENNReal.add_lt_top.mpr
    ⟨hs.tsum_ofReal_lt_top, hq.tsum_ofReal_lt_top⟩)).ne

end FreeProbability

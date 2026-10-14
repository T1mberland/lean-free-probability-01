import FreeProbability.RandomMatrix.OrthogonalBilinearConcentration
import FreeProbability.RandomMatrix.AlmostSureFromTails
import Mathlib.Probability.HasLaw
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Independent Haar-row bilinear forms under arbitrary cross-width couplings

Only the within-width joint law is specified. No independence between widths
is required. Conditional sphere sampling requires a separate law.
-/

namespace FreeProbability.Orthogonal

open Matrix MeasureTheory Filter ProbabilityTheory
open scoped Matrix.Norms.L2Operator ENNReal

theorem summable_bilinear_deviation_bounds (C ε : ℝ) (hε : 0 < ε) :
    Summable (fun k : ℕ => 3 * C ^ 4 / ((((k : ℝ) + 1) * ((k : ℝ) + 3)) * ε ^ 4)) := by
  have hp := (Real.summable_one_div_nat_pow (p := 2)).mpr (by decide)
  have hshift : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hp
  have hlarge := hshift.mul_left (3 * C ^ 4 / ε ^ 4)
  apply Summable.of_nonneg_of_le (fun k => by positivity) _ hlarge
  intro k
  have hk : 0 < (k : ℝ) + 1 := by positivity
  have hc : 0 ≤ 3 * C ^ 4 / ε ^ 4 := by positivity
  have hd : ((k : ℝ) + 1) ^ 2 ≤ ((k : ℝ) + 1) * ((k : ℝ) + 3) := by nlinarith
  calc
    _ = (3 * C ^ 4 / ε ^ 4) / (((k : ℝ) + 1) * ((k : ℝ) + 3)) := by
      simp only [div_div, mul_comm]
    _ ≤ (3 * C ^ 4 / ε ^ 4) / ((k : ℝ) + 1) ^ 2 :=
      div_le_div_of_nonneg_left hc (sq_pos_of_pos hk) hd
    _ = _ := by rw [mul_one_div]

/-- The same arbitrary-coupling limit holds for varying finite index types whose
first dimension has a positive linear lower bound. -/
theorem ae_bilinearRowForm_tendsto_zero_of_dimension_growth
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {n m : ℕ → Type*} [∀ k, Fintype (n k)] [∀ k, DecidableEq (n k)]
    [∀ k, Fintype (m k)] [∀ k, DecidableEq (m k)]
    (B : ∀ k, Matrix (n k) (m k) ℝ) (r : ∀ k, n k) (s : ∀ k, m k)
    (X : ∀ k, Ω → Group (n k) × Group (m k))
    (hX : ∀ k, HasLaw (X k) ((haar (n k)).prod (haar (m k))) μ)
    (C δ : ℝ) (hδ : 0 < δ) (hB : ∀ k, ‖B k‖ ≤ C)
    (hdim : ∀ k : ℕ, δ * ((k : ℝ) + 1) ≤ (Fintype.card (n k) : ℝ)) :
    ∀ᵐ ω ∂μ, Tendsto (fun k => bilinearRowForm (B k) (r k) (s k) (X k ω)) atTop (nhds 0) := by
  apply ae_tendsto_zero_of_summable_deviations
  intro ε hε
  let b := fun k : ℕ => (3 * C ^ 4 / (δ ^ 2 * ε ^ 4)) * (1 / ((k : ℝ) + 1) ^ 2)
  have ht (k : ℕ) : μ {ω | ε ≤ |bilinearRowForm (B k) (r k) (s k) (X k ω)|} ≤
      ENNReal.ofReal (b k) := by
    have hm : MeasurableSet {p | ε ≤ |bilinearRowForm (B k) (r k) (s k) p|} :=
      measurableSet_le measurable_const (continuous_bilinearRowForm _ _ _).abs.measurable
    rw [(hX k).measure_eq hm]
    apply (measure_bilinearRowForm_deviation_le (B k) (r k) (s k) ε hε).trans
    apply ENNReal.ofReal_le_ofReal
    have hk : 0 < (k : ℝ) + 1 := by positivity
    have hN : (0 : ℝ) < Fintype.card (n k) := (mul_pos hδ hk).trans_le (hdim k)
    have hsq : δ ^ 2 * ((k : ℝ) + 1) ^ 2 ≤ (Fintype.card (n k) : ℝ) ^ 2 := by
      simpa [mul_pow] using pow_le_pow_left₀ (mul_pos hδ hk).le (hdim k) 2
    have hd : δ ^ 2 * ((k : ℝ) + 1) ^ 2 ≤
        (Fintype.card (n k) : ℝ) * ((Fintype.card (n k) : ℝ) + 2) := by nlinarith
    have hn : ‖B k‖ ^ 4 ≤ C ^ 4 := pow_le_pow_left₀ (norm_nonneg _) (hB k) 4
    calc
      _ ≤ 3 * C ^ 4 /
          (((Fintype.card (n k) : ℝ) * ((Fintype.card (n k) : ℝ) + 2)) * ε ^ 4) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hn (by norm_num)) (by positivity)
      _ ≤ 3 * C ^ 4 / ((δ ^ 2 * ((k : ℝ) + 1) ^ 2) * ε ^ 4) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_right hd (by positivity))
      _ = b k := by
        dsimp [b]
        field_simp [hδ.ne', hε.ne', hk.ne']
  have hp := (Real.summable_one_div_nat_pow (p := 2)).mpr (by decide)
  have hshift : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hp
  have hb : (∑' k, ENNReal.ofReal (b k)) < ∞ :=
    (hshift.mul_left (3 * C ^ 4 / (δ ^ 2 * ε ^ 4))).tsum_ofReal_lt_top
  exact (lt_of_le_of_lt (ENNReal.tsum_le_tsum ht) hb).ne

/-- Independent Haar rows at each width give an almost-sure vanishing bilinear
form under any coupling between widths. The second dimension may vary freely. -/
theorem ae_bilinearRowForm_tendsto_zero {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (d : ℕ → ℕ) (B : ∀ k, Matrix (Fin (k + 1)) (Fin (d k + 1)) ℝ)
    (r : ∀ k, Fin (k + 1)) (s : ∀ k, Fin (d k + 1))
    (X : ∀ k, Ω → Group (Fin (k + 1)) × Group (Fin (d k + 1)))
    (hX : ∀ k, HasLaw (X k) ((haar (Fin (k + 1))).prod (haar (Fin (d k + 1)))) μ)
    (C : ℝ) (hB : ∀ k, ‖B k‖ ≤ C) :
    ∀ᵐ ω ∂μ, Tendsto (fun k => bilinearRowForm (B k) (r k) (s k) (X k ω)) atTop (nhds 0) := by
  apply ae_bilinearRowForm_tendsto_zero_of_dimension_growth μ B r s X hX C 1
    (by norm_num) hB
  intro k
  simp [Nat.cast_add, Nat.cast_one]

end FreeProbability.Orthogonal

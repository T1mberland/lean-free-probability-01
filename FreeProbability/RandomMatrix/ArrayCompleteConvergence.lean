import FreeProbability.RandomMatrix.IndependentFourthMoment
import FreeProbability.RandomMatrix.AlmostSureFromTails
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Probability.HasLaw

/-! # Complete convergence for independent arrays with fourth moments

Independence is required inside each finite row, with arbitrary coupling
between rows. The summable fourth-moment rate proves an almost-sure limit.
-/

namespace FreeProbability

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem measure_abs_ge_le_fourth_moment {Z : Ω → ℝ}
    (hZ : Integrable (fun ω => Z ω ^ 4) μ) (ε : ℝ) (hε : 0 < ε) :
    μ {ω | ε ≤ |Z ω|} ≤ ENNReal.ofReal ((∫ ω, Z ω ^ 4 ∂μ) / ε ^ 4) := by
  have he : {ω | ε ^ 4 ≤ Z ω ^ 4} = {ω | ε ≤ |Z ω|} := by
    ext ω
    change (ε ^ 4 ≤ Z ω ^ 4) ↔ ε ≤ |Z ω|
    rw [← (show Even 4 by decide).pow_abs (Z ω)]
    exact pow_le_pow_iff_left₀ (n := 4) hε.le (abs_nonneg _) (by decide)
  have h := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ω => (by positivity : 0 ≤ Z ω ^ 4))) hZ (ε ^ 4)
  rw [he] at h
  have hr : μ.real {ω | ε ≤ |Z ω|} ≤ (∫ ω, Z ω ^ 4 ∂μ) / ε ^ 4 := by
    apply (le_div_iff₀ (pow_pos hε 4)).mpr
    simpa [mul_comm] using h
  have ho := ENNReal.ofReal_le_ofReal hr
  rw [ofReal_measureReal] at ho
  exact ho

theorem measure_average_deviation_le {ι : Type*} {X : ι → Ω → ℝ}
    (hI : iIndepFun X μ) (hX : ∀ i, MemLp (X i) 4 μ)
    (h0 : ∀ i, (∫ ω, X i ω ∂μ) = 0) (M V : ℝ) (hM : 0 ≤ M)
    (h4 : ∀ i, (∫ ω, X i ω ^ 4 ∂μ) ≤ M)
    (h2 : ∀ i, (∫ ω, X i ω ^ 2 ∂μ) ≤ V) (s : Finset ι)
    (hN : (0 : ℝ) < s.card) (ε : ℝ) (hε : 0 < ε) :
    μ {ω | ε ≤ |(∑ i ∈ s, X i ω) / (s.card : ℝ)|} ≤
      ENNReal.ofReal ((M + 3 * V ^ 2) / ((s.card : ℝ) ^ 2 * ε ^ 4)) := by
  have hs : MemLp (fun ω => ∑ i ∈ s, X i ω) 4 μ := memLp_finsetSum s (fun i _ => hX i)
  have h := measure_abs_ge_le_fourth_moment
    (integrable_pow_of_memLp_four hs 4 (by norm_num)) ((s.card : ℝ) * ε) (mul_pos hN hε)
  have he : {ω | (s.card : ℝ) * ε ≤ |∑ i ∈ s, X i ω|} =
      {ω | ε ≤ |(∑ i ∈ s, X i ω) / (s.card : ℝ)|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, abs_div, abs_of_pos hN]
    rw [le_div_iff₀ hN, mul_comm ε]
  rw [he] at h
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ((s.card : ℝ) ^ 2 * (M + 3 * V ^ 2)) / ((s.card : ℝ) * ε) ^ 4 :=
      div_le_div_of_nonneg_right (integral_sum_pow_four_le hI hX h0 M V hM h4 h2 s)
        (by positivity)
    _ = _ := by field_simp [hN.ne', hε.ne']

/-- Uniform fourth moments yield almost-sure convergence of centered averages
for linearly growing independent rows. No cross-row independence is needed. -/
theorem ae_array_average_tendsto_zero {n : ℕ → Type*} [∀ k, Fintype (n k)]
    (X : ∀ k, n k → Ω → ℝ) (hI : ∀ k, iIndepFun (X k) μ)
    (hX : ∀ k i, MemLp (X k i) 4 μ) (h0 : ∀ k i, (∫ ω, X k i ω ∂μ) = 0)
    (M V δ : ℝ) (hM : 0 ≤ M) (hδ : 0 < δ)
    (h4 : ∀ k i, (∫ ω, X k i ω ^ 4 ∂μ) ≤ M)
    (h2 : ∀ k i, (∫ ω, X k i ω ^ 2 ∂μ) ≤ V)
    (hdim : ∀ k : ℕ, δ * ((k : ℝ) + 1) ≤ (Fintype.card (n k) : ℝ)) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun k => (∑ i, X k i ω) / (Fintype.card (n k) : ℝ)) atTop (nhds 0) := by
  classical
  apply ae_tendsto_zero_of_summable_deviations
  intro ε hε
  let C := M + 3 * V ^ 2
  let b := fun k : ℕ => (C / (δ ^ 2 * ε ^ 4)) * (1 / ((k : ℝ) + 1) ^ 2)
  have ht (k : ℕ) : μ {ω | ε ≤ |(∑ i, X k i ω) / (Fintype.card (n k) : ℝ)|} ≤
      ENNReal.ofReal (b k) := by
    have hk : 0 < (k : ℝ) + 1 := by positivity
    have hN : (0 : ℝ) < Fintype.card (n k) := (mul_pos hδ hk).trans_le (hdim k)
    have h := measure_average_deviation_le (hI k) (hX k) (h0 k) M V hM
      (h4 k) (h2 k) Finset.univ (by simpa using hN) ε hε
    simp only [Finset.card_univ] at h
    apply h.trans
    apply ENNReal.ofReal_le_ofReal
    have hs : δ ^ 2 * ((k : ℝ) + 1) ^ 2 ≤ (Fintype.card (n k) : ℝ) ^ 2 := by
      simpa [mul_pow] using pow_le_pow_left₀ (mul_pos hδ hk).le (hdim k) 2
    calc
      _ ≤ C / ((δ ^ 2 * ((k : ℝ) + 1) ^ 2) * ε ^ 4) :=
        div_le_div_of_nonneg_left (by dsimp [C]; positivity) (by positivity)
          (mul_le_mul_of_nonneg_right hs (by positivity))
      _ = b k := by dsimp [b]; field_simp [hδ.ne', hε.ne', hk.ne']
  have hp := (Real.summable_one_div_nat_pow (p := 2)).mpr (by decide)
  have hs : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hp
  have hb : (∑' k, ENNReal.ofReal (b k)) < ∞ :=
    (hs.mul_left (C / (δ ^ 2 * ε ^ 4))).tsum_ofReal_lt_top
  exact (lt_of_le_of_lt (ENNReal.tsum_le_tsum ht) hb).ne

/-- A finite fourth moment suffices for averages under finite product laws to
converge almost surely, for arbitrary couplings of the product-law rows. -/
theorem ae_product_law_average_tendsto {E : Type*} [MeasurableSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] (f : E → ℝ)
    (hf : Measurable f) (hF : MemLp f 4 ν)
    {n : ℕ → Type*} [∀ k, Fintype (n k)]
    (G : ∀ k, Ω → (n k → E))
    (hG : ∀ k, HasLaw (G k) (Measure.pi (fun _ : n k => ν)) μ)
    (δ : ℝ) (hδ : 0 < δ)
    (hdim : ∀ k : ℕ, δ * ((k : ℝ) + 1) ≤ (Fintype.card (n k) : ℝ)) :
    ∀ᵐ ω ∂μ, Tendsto (fun k => (∑ i, f (G k ω i)) / (Fintype.card (n k) : ℝ))
      atTop (nhds (∫ x, f x ∂ν)) := by
  classical
  let m := ∫ x, f x ∂ν
  let c := fun x => f x - m
  have hc : MemLp c 4 ν := hF.sub (memLp_const m)
  have hc0 : (∫ x, c x ∂ν) = 0 := by
    rw [show c = (fun x => f x - m) from rfl,
      integral_sub (hF.integrable (by norm_num)) (integrable_const m)]
    simp [m]
  have hcoord (k : ℕ) (i : n k) : HasLaw (fun ω => G k ω i) ν μ := by
    have he : HasLaw (Function.eval i) ν (Measure.pi (fun _ : n k => ν)) :=
      ⟨(measurable_pi_apply i).aemeasurable, by simp [Measure.pi_map_eval]⟩
    exact he.fun_comp (hG k)
  let X := fun k (i : n k) ω => c (G k ω i)
  have hi (k : ℕ) : iIndepFun (X k) μ := by
    have h := (iIndepFun_iff_hasLaw_pi_pi (hcoord k)).mpr (hG k)
    exact h.comp (fun _ => c) (fun _ => hf.sub measurable_const)
  have hx (k : ℕ) (i : n k) : MemLp (X k i) 4 μ := (hcoord k i).memLp_comp hc
  have h0 (k : ℕ) (i : n k) : (∫ ω, X k i ω ∂μ) = 0 := by
    have h := (hcoord k i).integral_comp hc.aestronglyMeasurable
    simpa only [Function.comp_def, hc0] using h
  let M := ∫ x, c x ^ 4 ∂ν
  let V := ∫ x, c x ^ 2 ∂ν
  have h4 (k : ℕ) (i : n k) : (∫ ω, X k i ω ^ 4 ∂μ) ≤ M := by
    exact ((hcoord k i).integral_comp (hc.aestronglyMeasurable.pow 4)).le
  have h2 (k : ℕ) (i : n k) : (∫ ω, X k i ω ^ 2 ∂μ) ≤ V := by
    exact ((hcoord k i).integral_comp (hc.aestronglyMeasurable.pow 2)).le
  have hlim := ae_array_average_tendsto_zero X hi hx h0 M V δ
    (integral_nonneg (fun x => by positivity)) hδ h4 h2 hdim
  filter_upwards [hlim] with ω hω
  have hm : Tendsto (fun _ : ℕ => m) atTop (nhds m) := tendsto_const_nhds
  have h := hω.add hm
  have he (k : ℕ) : ((∑ i, X k i ω) / (Fintype.card (n k) : ℝ)) + m =
      (∑ i, f (G k ω i)) / (Fintype.card (n k) : ℝ) := by
    have hN : (0 : ℝ) < Fintype.card (n k) :=
      (mul_pos hδ (by positivity)).trans_le (hdim k)
    simp only [X, c, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp [hN.ne']
    ring
  simpa only [he, zero_add] using h

/-- A nonnegative coefficient for fourth-moment average deviation bounds. -/
noncomputable def averageFourthMomentBound {E : Type*} [MeasurableSpace E]
    (ν : Measure E) (f : E → ℝ) : ℝ :=
  (∫ x, (f x - ∫ y, f y ∂ν) ^ 4 ∂ν) +
    3 * (∫ x, (f x - ∫ y, f y ∂ν) ^ 2 ∂ν) ^ 2

theorem averageFourthMomentBound_nonneg {E : Type*} [MeasurableSpace E]
    (ν : Measure E) (f : E → ℝ) : 0 ≤ averageFourthMomentBound ν f := by
  unfold averageFourthMomentBound
  exact add_nonneg (integral_nonneg (fun _ => by positivity)) (by positivity)

theorem measure_product_average_deviation_le {E : Type*} [MeasurableSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] (f : E → ℝ)
    (hf : Measurable f) (hF : MemLp f 4 ν) {n : Type*} [Fintype n]
    (hN : (0 : ℝ) < Fintype.card n) (ε : ℝ) (hε : 0 < ε) :
    (Measure.pi (fun _ : n => ν)) {g | ε ≤
      |(∑ i, f (g i)) / (Fintype.card n : ℝ) - ∫ x, f x ∂ν|} ≤
        ENNReal.ofReal (averageFourthMomentBound ν f / ((Fintype.card n : ℝ) ^ 2 * ε ^ 4)) := by
  classical
  let m := ∫ x, f x ∂ν
  let c := fun x => f x - m
  have hc : MemLp c 4 ν := hF.sub (memLp_const m)
  have hc0 : (∫ x, c x ∂ν) = 0 := by
    rw [show c = (fun x => f x - m) from rfl,
      integral_sub (hF.integrable (by norm_num)) (integrable_const m)]
    simp [m]
  have hl (i : n) : HasLaw (Function.eval i) ν (Measure.pi (fun _ : n => ν)) :=
    ⟨(measurable_pi_apply i).aemeasurable, by simp [Measure.pi_map_eval]⟩
  let X := fun i : n => fun g : n → E => c (g i)
  have hi : iIndepFun X (Measure.pi (fun _ : n => ν)) := iIndepFun_pi (fun _ => (hf.sub measurable_const).aemeasurable)
  have hx (i : n) : MemLp (X i) 4 (Measure.pi (fun _ : n => ν)) := (hl i).memLp_comp hc
  have h0 (i : n) : (∫ g, X i g ∂Measure.pi (fun _ : n => ν)) = 0 := by
    simpa only [Function.comp_def, hc0] using (hl i).integral_comp hc.aestronglyMeasurable
  let M := ∫ x, c x ^ 4 ∂ν
  let V := ∫ x, c x ^ 2 ∂ν
  have h4 (i : n) : (∫ g, X i g ^ 4 ∂Measure.pi (fun _ : n => ν)) ≤ M :=
    ((hl i).integral_comp (hc.aestronglyMeasurable.pow 4)).le
  have h2 (i : n) : (∫ g, X i g ^ 2 ∂Measure.pi (fun _ : n => ν)) ≤ V :=
    ((hl i).integral_comp (hc.aestronglyMeasurable.pow 2)).le
  have h := measure_average_deviation_le hi hx h0 M V (integral_nonneg (fun _ => by positivity))
    h4 h2 Finset.univ (by simpa using hN) ε hε
  have he (g : n → E) : (∑ i, X i g) / (Fintype.card n : ℝ) =
      (∑ i, f (g i)) / (Fintype.card n : ℝ) - m := by
    simp only [X, c, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp [hN.ne']
  simpa only [Finset.card_univ, he, M, V, c, m, averageFourthMomentBound] using h

end FreeProbability

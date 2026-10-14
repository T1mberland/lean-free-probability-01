import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Fourth moments of centered independent sums -/

namespace FreeProbability

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem integrable_pow_of_memLp_four {X : Ω → ℝ} (hX : MemLp X 4 μ)
    (p : ℕ) (hp : p ≤ 4) : Integrable (fun ω => X ω ^ p) μ := by
  have h : MemLp X (p : ℝ≥0∞) μ := hX.mono_exponent (by exact_mod_cast hp)
  have hn := h.integrable_norm_pow'
  apply (integrable_norm_iff (hX.aestronglyMeasurable.pow p)).mp
  simpa only [Pi.pow_apply, norm_pow] using hn

theorem integral_add_pow_two_of_indep {X Y : Ω → ℝ}
    (hXY : IndepFun X Y μ) (hX : MemLp X 4 μ) (hY : MemLp Y 4 μ)
    (hX0 : (∫ ω, X ω ∂μ) = 0) (hY0 : (∫ ω, Y ω ∂μ) = 0) :
    (∫ ω, (X ω + Y ω) ^ 2 ∂μ) =
      (∫ ω, X ω ^ 2 ∂μ) + (∫ ω, Y ω ^ 2 ∂μ) := by
  have hx := integrable_pow_of_memLp_four hX 2 (by norm_num)
  have hy := integrable_pow_of_memLp_four hY 2 (by norm_num)
  have hxy := hXY.integrable_mul (hX.integrable (by norm_num)) (hY.integrable (by norm_num))
  have hexp : (fun ω => (X ω + Y ω) ^ 2) =
      (fun ω => X ω ^ 2 + 2 * (X ω * Y ω) + Y ω ^ 2) := by funext ω; ring
  have ha := integral_add (hx.add (hxy.const_mul 2)) hy
  have hb := integral_add hx (hxy.const_mul 2)
  simp only [Pi.add_apply, Pi.mul_apply] at ha hb
  rw [hexp, ha, hb, integral_const_mul,
    hXY.integral_fun_mul_eq_mul_integral hX.aestronglyMeasurable hY.aestronglyMeasurable, hX0, hY0]
  ring

theorem integral_add_pow_four_of_indep {X Y : Ω → ℝ}
    (hXY : IndepFun X Y μ) (hX : MemLp X 4 μ) (hY : MemLp Y 4 μ)
    (hX0 : (∫ ω, X ω ∂μ) = 0) (hY0 : (∫ ω, Y ω ∂μ) = 0) :
    (∫ ω, (X ω + Y ω) ^ 4 ∂μ) =
      (∫ ω, X ω ^ 4 ∂μ) + 6 * (∫ ω, X ω ^ 2 ∂μ) * (∫ ω, Y ω ^ 2 ∂μ) +
        (∫ ω, Y ω ^ 4 ∂μ) := by
  have hi (a b : ℕ) : IndepFun (fun ω => X ω ^ a) (fun ω => Y ω ^ b) μ :=
    hXY.comp (measurable_id.pow_const a) (measurable_id.pow_const b)
  have hp (a b : ℕ) (ha : a ≤ 4) (hb : b ≤ 4) :
      Integrable (fun ω => X ω ^ a * Y ω ^ b) μ :=
    (hi a b).integrable_mul (integrable_pow_of_memLp_four hX a ha)
      (integrable_pow_of_memLp_four hY b hb)
  have he (a b : ℕ) : (∫ ω, X ω ^ a * Y ω ^ b ∂μ) =
      (∫ ω, X ω ^ a ∂μ) * (∫ ω, Y ω ^ b ∂μ) :=
    (hi a b).integral_fun_mul_eq_mul_integral
      (hX.aestronglyMeasurable.pow a) (hY.aestronglyMeasurable.pow b)
  have h4x := integrable_pow_of_memLp_four hX 4 (by norm_num)
  have h4y := integrable_pow_of_memLp_four hY 4 (by norm_num)
  have h31 := (hp 3 1 (by norm_num) (by norm_num)).const_mul 4
  have h22 := (hp 2 2 (by norm_num) (by norm_num)).const_mul 6
  have h13 := (hp 1 3 (by norm_num) (by norm_num)).const_mul 4
  have hexp : (fun ω => (X ω + Y ω) ^ 4) = (fun ω =>
      X ω ^ 4 + 4 * (X ω ^ 3 * Y ω ^ 1) + 6 * (X ω ^ 2 * Y ω ^ 2) +
        4 * (X ω ^ 1 * Y ω ^ 3) + Y ω ^ 4) := by funext ω; ring
  have ha := integral_add (((h4x.add h31).add h22).add h13) h4y
  have hb := integral_add ((h4x.add h31).add h22) h13
  have hc := integral_add (h4x.add h31) h22
  have hd := integral_add h4x h31
  simp only [Pi.add_apply] at ha hb hc hd
  rw [hexp, ha, hb, hc, hd,
    integral_const_mul, integral_const_mul, integral_const_mul, he 3 1, he 2 2, he 1 3]
  simp only [pow_one, hX0, hY0, mul_zero, zero_mul, add_zero]
  ring

variable {ι : Type*} {X : ι → Ω → ℝ}

theorem integral_sum_pow_two_of_iIndep (hI : iIndepFun X μ)
    (hX : ∀ i, MemLp (X i) 4 μ) (h0 : ∀ i, (∫ ω, X i ω ∂μ) = 0) (s : Finset ι) :
    (∫ ω, (∑ i ∈ s, X i ω) ^ 2 ∂μ) = ∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
    have hs : MemLp (fun ω => ∑ j ∈ s, X j ω) 4 μ := memLp_finsetSum s (fun j _ => hX j)
    have hs0 : (∫ ω, ∑ j ∈ s, X j ω ∂μ) = 0 := by
      rw [integral_finsetSum s (fun j _ => (hX j).integrable (by norm_num))]
      simp [h0]
    have hi : IndepFun (X i) (fun ω => ∑ j ∈ s, X j ω) μ := by
      have h := (hI.indepFun_finsetSum_of_notMem₀ (fun j => (hX j).aemeasurable) his).symm
      have he : (∑ j ∈ s, X j) = (fun ω => ∑ j ∈ s, X j ω) := by ext ω; simp
      rw [he] at h
      exact h
    simp only [Finset.sum_insert his]
    rw [integral_add_pow_two_of_indep hi (hX i) hs (h0 i) hs0, ih]

/-- Exact fourth moment for any finite centered independent family. The
individual laws need not coincide. -/
theorem integral_sum_pow_four_of_iIndep (hI : iIndepFun X μ)
    (hX : ∀ i, MemLp (X i) 4 μ) (h0 : ∀ i, (∫ ω, X i ω ∂μ) = 0) (s : Finset ι) :
    (∫ ω, (∑ i ∈ s, X i ω) ^ 4 ∂μ) =
      (∑ i ∈ s, ∫ ω, X i ω ^ 4 ∂μ) + 3 * (∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ) ^ 2 -
        3 * (∑ i ∈ s, (∫ ω, X i ω ^ 2 ∂μ) ^ 2) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
    have hs : MemLp (fun ω => ∑ j ∈ s, X j ω) 4 μ := memLp_finsetSum s (fun j _ => hX j)
    have hs0 : (∫ ω, ∑ j ∈ s, X j ω ∂μ) = 0 := by
      rw [integral_finsetSum s (fun j _ => (hX j).integrable (by norm_num))]
      simp [h0]
    have hi : IndepFun (X i) (fun ω => ∑ j ∈ s, X j ω) μ := by
      have h := (hI.indepFun_finsetSum_of_notMem₀ (fun j => (hX j).aemeasurable) his).symm
      have he : (∑ j ∈ s, X j) = (fun ω => ∑ j ∈ s, X j ω) := by ext ω; simp
      rw [he] at h
      exact h
    simp only [Finset.sum_insert his]
    rw [integral_add_pow_four_of_indep hi (hX i) hs (h0 i) hs0, ih,
      integral_sum_pow_two_of_iIndep hI hX h0 s]
    ring

/-- Uniform second and fourth moments give a quadratic dimension bound. -/
theorem integral_sum_pow_four_le (hI : iIndepFun X μ)
    (hX : ∀ i, MemLp (X i) 4 μ) (h0 : ∀ i, (∫ ω, X i ω ∂μ) = 0)
    (M V : ℝ) (hM : 0 ≤ M)
    (h4 : ∀ i, (∫ ω, X i ω ^ 4 ∂μ) ≤ M)
    (h2 : ∀ i, (∫ ω, X i ω ^ 2 ∂μ) ≤ V) (s : Finset ι) :
    (∫ ω, (∑ i ∈ s, X i ω) ^ 4 ∂μ) ≤ (s.card : ℝ) ^ 2 * (M + 3 * V ^ 2) := by
  classical
  by_cases hs : s = ∅
  · simp [hs]
  have hN : (1 : ℝ) ≤ s.card := by
    exact_mod_cast (Nat.succ_le_iff.mpr
      (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hs)))
  have hN0 : (0 : ℝ) ≤ s.card := by positivity
  have hm : (∑ i ∈ s, ∫ ω, X i ω ^ 4 ∂μ) ≤ (s.card : ℝ) * M := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum (fun i _ => h4 i)
  have hv : (∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ) ≤ (s.card : ℝ) * V := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum (fun i _ => h2 i)
  have hv0 : 0 ≤ ∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ :=
    Finset.sum_nonneg (fun i _ => integral_nonneg (fun _ => sq_nonneg _))
  have hvv := pow_le_pow_left₀ hv0 hv 2
  have hrest : 0 ≤ 3 * ∑ i ∈ s, (∫ ω, X i ω ^ 2 ∂μ) ^ 2 := by positivity
  have hnm : (s.card : ℝ) * M ≤ (s.card : ℝ) ^ 2 * M :=
    mul_le_mul_of_nonneg_right (by nlinarith) hM
  rw [integral_sum_pow_four_of_iIndep hI hX h0]
  nlinarith

end FreeProbability

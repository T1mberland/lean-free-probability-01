import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Combinatorics.Enumerative.Catalan.Basic

/-! # Weighted square-root integrals for the explicit variance-one semicircle density -/

noncomputable section
open scoped Real
open Real intervalIntegral Set

namespace FreeProbability.Semicircular

/-- Trigonometric moments on the half-circle interval. -/
def cosMoment (n : ℕ) : ℝ := ∫ θ in (0 : ℝ)..π, cos θ ^ n

@[simp] theorem cosMoment_zero : cosMoment 0 = π := by simp [cosMoment]
@[simp] theorem cosMoment_one : cosMoment 1 = 0 := by simp [cosMoment]

/-- Exact integration-by-parts recurrence, including every parity. -/
theorem cosMoment_succ_succ (n : ℕ) :
    cosMoment (n + 2) = (n + 1 : ℝ) / (n + 2) * cosMoment n := by
  simpa [cosMoment] using integral_cos_pow (a := 0) (b := π) n

/-- The exact even cosine integral in terms of the central binomial coefficient. -/
theorem cosMoment_even (n : ℕ) :
    cosMoment (2 * n) * 4 ^ n = π * (Nat.centralBinom n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hrec := cosMoment_succ_succ (2 * n)
    have hbin := congrArg (fun k : ℕ => (k : ℝ)) (Nat.succ_mul_centralBinom_succ n)
    push_cast at hbin
    have hpow : (4 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    have hc : cosMoment (2 * n) = π * (Nat.centralBinom n : ℝ) / 4 ^ n :=
      (eq_div_iff hpow).mpr ih
    rw [show 2 * (n + 1) = 2 * n + 2 by omega, hrec, hc, pow_succ]
    push_cast
    field_simp
    nlinarith [hbin]

/-- All odd cosine moments vanish by the genuine integration-by-parts recurrence. -/
theorem cosMoment_odd (n : ℕ) : cosMoment (2 * n + 1) = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega, cosMoment_succ_succ, ih, mul_zero]

/-- Actual weighted square-root moments before probability normalization. -/
def weightedSqrtMoment (n : ℕ) : ℝ := ∫ x in (-2 : ℝ)..2, x ^ n * √(4 - x ^ 2)

/-- The genuine cosine substitution evaluates weighted moments as a difference of cosine moments. -/
theorem weightedSqrtMoment_eq_cosMoment (n : ℕ) :
    weightedSqrtMoment n = 4 * 2 ^ n * (cosMoment n - cosMoment (n + 2)) := by
  have hsub := integral_comp_mul_deriv
    (a := 0) (b := π) (f := fun θ => 2 * cos θ) (f' := fun θ => 2 * (-sin θ))
    (g := fun x => x ^ n * √(4 - x ^ 2))
    (fun θ _ => (hasDerivAt_cos θ).const_mul 2) (by fun_prop) (by fun_prop)
  simp only [cos_zero, cos_pi, mul_one, mul_neg_one] at hsub
  have hs : weightedSqrtMoment n = - ∫ θ in (0 : ℝ)..π,
      (2 * cos θ) ^ n * √(4 - (2 * cos θ) ^ 2) * (2 * (-sin θ)) := by
    calc
      weightedSqrtMoment n = -(∫ x in (2 : ℝ)..(-2), x ^ n * √(4 - x ^ 2)) := by
        rw [integral_symm]
        simp only [neg_neg, weightedSqrtMoment]
      _ = _ := congrArg (fun x : ℝ => -x) hsub.symm
  have hint : (∫ θ in (0 : ℝ)..π,
      (2 * cos θ) ^ n * √(4 - (2 * cos θ) ^ 2) * (2 * (-sin θ))) =
      (∫ θ in (0 : ℝ)..π, -(4 * 2 ^ n) * (cos θ ^ n - cos θ ^ (n + 2))) := by
    apply integral_congr_ae
    apply MeasureTheory.ae_of_all
    intro θ hθ
    rw [uIoc_of_le pi_pos.le, Set.mem_Ioc] at hθ
    have hsin := sin_nonneg_of_nonneg_of_le_pi hθ.1.le hθ.2
    have hsq : 4 - (2 * cos θ) ^ 2 = (2 * sin θ) ^ 2 := by
      nlinarith [sin_sq_add_cos_sq θ]
    have hsqrt : √(4 - (2 * cos θ) ^ 2) = 2 * sin θ := by
      rw [hsq, sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) hsin)]
    have hsinSq : sin θ ^ 2 = 1 - cos θ ^ 2 := by nlinarith [sin_sq_add_cos_sq θ]
    rw [hsqrt, mul_pow]
    calc
      2 ^ n * cos θ ^ n * (2 * sin θ) * (2 * -sin θ) =
          -(4 * 2 ^ n) * (cos θ ^ n * sin θ ^ 2) := by ring
      _ = -(4 * 2 ^ n) * (cos θ ^ n - cos θ ^ (n + 2)) := by
        rw [hsinSq, pow_add]
        ring
  rw [hs, hint, integral_const_mul, integral_sub (f := fun θ => cos θ ^ n) (g := fun θ => cos θ ^ (n + 2))
    ((continuous_cos.pow n).intervalIntegrable 0 π)
    ((continuous_cos.pow (n + 2)).intervalIntegrable 0 π)]
  simp only [cosMoment, neg_mul, neg_neg]

/-- Exact all-order even weighted square-root integrals are Catalan numbers before normalization. -/
theorem weightedSqrtMoment_even (n : ℕ) : weightedSqrtMoment (2 * n) = 2 * π * (catalan n : ℝ) := by
  have hpow : (4 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hc : cosMoment (2 * n) = π * (Nat.centralBinom n : ℝ) / 4 ^ n :=
    (eq_div_iff hpow).mpr (cosMoment_even n)
  have hcat := congrArg (fun k : ℕ => (k : ℝ)) (succ_mul_catalan_eq_centralBinom n)
  push_cast at hcat
  rw [weightedSqrtMoment_eq_cosMoment, cosMoment_succ_succ, hc, pow_mul]
  norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num]
  push_cast
  rw [← hcat]
  field_simp
  ring

/-- Exact all-order odd weighted square-root integrals vanish. -/
theorem weightedSqrtMoment_odd (n : ℕ) : weightedSqrtMoment (2 * n + 1) = 0 := by
  rw [weightedSqrtMoment_eq_cosMoment, cosMoment_odd,
    show (2 * n + 1) + 2 = 2 * (n + 1) + 1 by omega, cosMoment_odd]
  ring

/-- The explicit variance-one semicircle density on the real line. -/
def semicircleDensity (x : ℝ) : ℝ := √(4 - x ^ 2) / (2 * π)

theorem continuous_semicircleDensity : Continuous semicircleDensity := by
  unfold semicircleDensity
  fun_prop

theorem semicircleDensity_nonneg (x : ℝ) : 0 ≤ semicircleDensity x := by
  unfold semicircleDensity
  positivity

theorem semicircleDensity_eq_zero_of_notMem {x : ℝ} (hx : x ∉ Icc (-2 : ℝ) 2) :
    semicircleDensity x = 0 := by
  have hs : 4 - x ^ 2 ≤ 0 := by
    simp only [mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx <;> nlinarith
  simp [semicircleDensity, sqrt_eq_zero_of_nonpos hs]

/-- The explicit density has the actual Catalan even integral moments. -/
theorem integral_semicircleDensity_even (n : ℕ) :
    (∫ x in (-2 : ℝ)..2, x ^ (2 * n) * semicircleDensity x) = (catalan n : ℝ) := by
  have he : (fun x : ℝ => x ^ (2 * n) * semicircleDensity x) =
      fun x => (x ^ (2 * n) * √(4 - x ^ 2)) / (2 * π) := by
    funext x
    simp only [semicircleDensity]
    ring
  rw [he, integral_div]
  change weightedSqrtMoment (2 * n) / (2 * π) = _
  rw [weightedSqrtMoment_even]
  field_simp

/-- The explicit density has actual vanishing odd integral moments. -/
theorem integral_semicircleDensity_odd (n : ℕ) :
    (∫ x in (-2 : ℝ)..2, x ^ (2 * n + 1) * semicircleDensity x) = 0 := by
  have he : (fun x : ℝ => x ^ (2 * n + 1) * semicircleDensity x) =
      fun x => (x ^ (2 * n + 1) * √(4 - x ^ 2)) / (2 * π) := by
    funext x
    simp only [semicircleDensity]
    ring
  rw [he, integral_div]
  change weightedSqrtMoment (2 * n + 1) / (2 * π) = _
  rw [weightedSqrtMoment_odd, zero_div]

/-- Probability normalization is a consequence of the actual zeroth density moment. -/
@[simp] theorem integral_semicircleDensity : (∫ x in (-2 : ℝ)..2, semicircleDensity x) = 1 := by
  simpa using integral_semicircleDensity_even 0

end FreeProbability.Semicircular

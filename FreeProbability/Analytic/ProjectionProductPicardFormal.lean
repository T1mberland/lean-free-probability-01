import FreeProbability.Analytic.ProjectionProductPicardStabilization
import Mathlib.RingTheory.PowerSeries.Basic

/-! # Exact formal equation of the genuinely summable Picard coefficients -/

noncomputable section
namespace FreeProbability

/-- Products preserve agreement of power-series coefficients below an order. -/
theorem powerSeries_coeff_mul_congr_below {R : Type*} [Semiring R]
    (p q a b : PowerSeries R) (N : ℕ)
    (hpq : ∀ n < N, PowerSeries.coeff n p = PowerSeries.coeff n q)
    (hab : ∀ n < N, PowerSeries.coeff n a = PowerSeries.coeff n b)
    (n : ℕ) (hn : n < N) :
    PowerSeries.coeff n (p * a) = PowerSeries.coeff n (q * b) := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have he : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
  rw [hpq ij.1 (by omega), hab ij.2 (by omega)]

/-- Powers preserve agreement of power-series coefficients below an order. -/
theorem powerSeries_coeff_pow_congr_below {R : Type*} [Semiring R]
    (p q : PowerSeries R) (N : ℕ)
    (hpq : ∀ n < N, PowerSeries.coeff n p = PowerSeries.coeff n q) (L : ℕ) :
    ∀ n < N, PowerSeries.coeff n (p ^ L) = PowerSeries.coeff n (q ^ L) := by
  induction L with
  | zero => intro n _; rfl
  | succ L ih =>
    intro n hn
    rw [pow_succ, pow_succ]
    exact powerSeries_coeff_mul_congr_below (p ^ L) (q ^ L) p q N ih hpq n hn

/-- The formal series of the already genuinely summable stabilized coefficients. -/
def halfProjectionPicardSeries (L : ℕ) : PowerSeries ℝ :=
  PowerSeries.mk (halfProjectionPicardCoefficient L)

@[simp] theorem halfProjectionPicardSeries_coeff (L n : ℕ) :
    PowerSeries.coeff n (halfProjectionPicardSeries L) = halfProjectionPicardCoefficient L n :=
  PowerSeries.coeff_mk n _

/-- The formal Picard limit solves the exact normalized implicit equation. -/
theorem halfProjectionPicardSeries_equation (L : ℕ) :
    halfProjectionPicardSeries L = PowerSeries.C ((2 : ℝ) ^ L)⁻¹ * PowerSeries.X *
      (1 + halfProjectionPicardSeries L) ^ L := by
  ext n
  cases n with
  | zero => simp [halfProjectionPicardCoefficient, halfProjectionPicardPolynomial, mul_assoc]
  | succ n =>
    rw [halfProjectionPicardSeries_coeff, halfProjectionPicardCoefficient]
    change (Polynomial.C ((2 : ℝ) ^ L)⁻¹ * Polynomial.X *
      (1 + halfProjectionPicardPolynomial L (n + 1)) ^ L).coeff (n + 1) = _
    simp only [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul]
    congr 1
    have he : PowerSeries.coeff n
        ((1 + (halfProjectionPicardPolynomial L (n + 1) : PowerSeries ℝ)) ^ L) =
        PowerSeries.coeff n ((1 + halfProjectionPicardSeries L) ^ L) := by
      apply powerSeries_coeff_pow_congr_below _ _ (n + 1) _ L n (by omega)
      intro j hj
      simp only [map_add, Polynomial.coeff_coe, halfProjectionPicardSeries_coeff]
      congr 1
      exact halfProjectionPicardPolynomial_coeff_stable L j (n + 1) hj
    simpa only [← Polynomial.coe_one, ← Polynomial.coe_add, ← Polynomial.coe_pow, Polynomial.coeff_coe] using he

/-- The normalized implicit equation has at most one formal solution over
any semiring, including complex analytic coefficients. -/
theorem powerSeries_implicit_equation_unique {R : Type*} [Semiring R]
    (L : ℕ) (c : R) (Q P : PowerSeries R)
    (hQ : Q = PowerSeries.C c * PowerSeries.X * (1 + Q) ^ L)
    (hP : P = PowerSeries.C c * PowerSeries.X * (1 + P) ^ L) : Q = P := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => rw [hQ, hP]; simp [mul_assoc]
    | succ n =>
      nth_rw 1 [hQ]
      conv_rhs => rw [hP]
      simp only [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul]
      congr 1
      apply powerSeries_coeff_pow_congr_below _ _ (n + 1) _ L n (by omega)
      intro j hj
      simp only [map_add]
      rw [ih j hj]

/-- The normalized implicit formal equation determines the Picard series
uniquely. Identifying the actual analytic germ is a separate step. -/
theorem halfProjectionPicardSeries_unique (L : ℕ) (Q : PowerSeries ℝ)
    (hQ : Q = PowerSeries.C ((2 : ℝ) ^ L)⁻¹ * PowerSeries.X * (1 + Q) ^ L) :
    Q = halfProjectionPicardSeries L :=
  powerSeries_implicit_equation_unique L _ Q _ hQ (halfProjectionPicardSeries_equation L)
end FreeProbability

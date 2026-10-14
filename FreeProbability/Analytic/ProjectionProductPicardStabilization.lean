import FreeProbability.Analytic.ProjectionProductPicardPolynomial

/-! # Stabilization and genuine summability of Picard limit coefficients -/

noncomputable section
open scoped BigOperators
namespace FreeProbability

/-- Multiplication preserves agreement of coefficients below a fixed order. -/
theorem polynomial_coeff_mul_congr_below {R : Type*} [Semiring R]
    (p q a b : Polynomial R) (N : ℕ)
    (hpq : ∀ n < N, p.coeff n = q.coeff n)
    (hab : ∀ n < N, a.coeff n = b.coeff n) (n : ℕ) (hn : n < N) :
    (p * a).coeff n = (q * b).coeff n := by
  rw [Polynomial.coeff_mul, Polynomial.coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have he : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
  rw [hpq ij.1 (by omega), hab ij.2 (by omega)]

/-- Powers preserve agreement of coefficients below a fixed order. -/
theorem polynomial_coeff_pow_congr_below {R : Type*} [Semiring R]
    (p q : Polynomial R) (N : ℕ) (hpq : ∀ n < N, p.coeff n = q.coeff n) (L : ℕ) :
    ∀ n < N, (p ^ L).coeff n = (q ^ L).coeff n := by
  induction L with
  | zero => intro n _; rfl
  | succ L ih =>
    intro n hn
    rw [pow_succ, pow_succ]
    exact polynomial_coeff_mul_congr_below (p ^ L) (q ^ L) p q N ih hpq n hn

/-- The first `k` coefficients have stopped changing after `k` Picard steps. -/
theorem halfProjectionPicardPolynomial_coeff_step_stable (L k : ℕ) :
    ∀ n < k, (halfProjectionPicardPolynomial L (k + 1)).coeff n =
      (halfProjectionPicardPolynomial L k).coeff n := by
  induction k with
  | zero => intro n hn; omega
  | succ k ih =>
    intro n hn
    cases n with
    | zero => simp [halfProjectionPicardPolynomial, Polynomial.coeff_mul]
    | succ n =>
      change (Polynomial.C ((2 : ℝ) ^ L)⁻¹ * Polynomial.X *
        (1 + halfProjectionPicardPolynomial L (k + 1)) ^ L).coeff (n + 1) =
        (Polynomial.C ((2 : ℝ) ^ L)⁻¹ * Polynomial.X *
          (1 + halfProjectionPicardPolynomial L k) ^ L).coeff (n + 1)
      simp only [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul]
      congr 1
      apply polynomial_coeff_pow_congr_below _ _ k _ L n (by omega)
      intro j hj
      rw [Polynomial.coeff_add, Polynomial.coeff_add, ih j hj]

/-- Once stabilized, a coefficient remains unchanged at every later step. -/
theorem halfProjectionPicardPolynomial_coeff_stable (L n k : ℕ) (hk : n < k) :
    (halfProjectionPicardPolynomial L k).coeff n =
      (halfProjectionPicardPolynomial L (n + 1)).coeff n := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases he : k = n
    · subst k; rfl
    · rw [halfProjectionPicardPolynomial_coeff_step_stable L k n (by omega), ih (by omega)]

/-- The genuine stabilized nonnegative coefficient sequence of Picard iteration. -/
def halfProjectionPicardCoefficient (L n : ℕ) : ℝ :=
  (halfProjectionPicardPolynomial L (n + 1)).coeff n

theorem halfProjectionPicardCoefficient_nonneg (L n : ℕ) :
    0 ≤ halfProjectionPicardCoefficient L n :=
  halfProjectionPicardPolynomial_coeff_nonneg L (n + 1) n

/-- The stabilized infinite coefficient sequence has bounded finite sums. -/
theorem halfProjectionPicardCoefficient_partial_sum_le_supersolution
    (L N : ℕ) (t : ℝ) (ht : 0 ≤ t) (r : ℝ) (hr : 0 ≤ r)
    (hsuper : (t / (2 : ℝ) ^ L) * (1 + r) ^ L ≤ r) :
    (∑ n ∈ Finset.range N, halfProjectionPicardCoefficient L n * t ^ n) ≤ r := by
  have he : (∑ n ∈ Finset.range N, halfProjectionPicardCoefficient L n * t ^ n) =
      ∑ n ∈ Finset.range N, (halfProjectionPicardPolynomial L N).coeff n * t ^ n := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [halfProjectionPicardCoefficient,
      halfProjectionPicardPolynomial_coeff_stable L n N (Finset.mem_range.mp hn)]
  rw [he]
  exact halfProjectionPicardPolynomial_partial_sum_le_supersolution L N N t ht r hr hsuper

/-- A nonnegative scalar supersolution proves genuine convergence of the
stabilized coefficient series, rather than merely formal positivity. -/
theorem halfProjectionPicardCoefficient_summable (L : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (r : ℝ) (hr : 0 ≤ r) (hsuper : (t / (2 : ℝ) ^ L) * (1 + r) ^ L ≤ r) :
    Summable (fun n : ℕ => halfProjectionPicardCoefficient L n * t ^ n) := by
  apply summable_of_sum_range_le
    (fun n => mul_nonneg (halfProjectionPicardCoefficient_nonneg L n) (pow_nonneg ht n))
  intro N
  exact halfProjectionPicardCoefficient_partial_sum_le_supersolution L N t ht r hr hsuper
/-- The genuinely convergent stabilized series obeys the same scalar bound. -/
theorem halfProjectionPicardCoefficient_tsum_le_supersolution (L : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (r : ℝ) (hr : 0 ≤ r) (hsuper : (t / (2 : ℝ) ^ L) * (1 + r) ^ L ≤ r) :
    (∑' n : ℕ, halfProjectionPicardCoefficient L n * t ^ n) ≤ r :=
  (halfProjectionPicardCoefficient_summable L t ht r hr hsuper).tsum_le_of_sum_range_le
    (fun N => halfProjectionPicardCoefficient_partial_sum_le_supersolution L N t ht r hr hsuper)
end FreeProbability

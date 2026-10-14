import FreeProbability.Analytic.ProjectionProductPicard
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # Nonnegative polynomial Picard approximants and quantitative partial-sum bounds -/

noncomputable section
open scoped BigOperators
namespace FreeProbability

private theorem nonneg_coeff_mul (p q : Polynomial ℝ)
    (hp : ∀ n, 0 ≤ p.coeff n) (hq : ∀ n, 0 ≤ q.coeff n) :
    ∀ n, 0 ≤ (p * q).coeff n := by
  intro n
  rw [Polynomial.coeff_mul]
  exact Finset.sum_nonneg (fun ij _ => mul_nonneg (hp ij.1) (hq ij.2))

private theorem nonneg_coeff_pow (p : Polynomial ℝ) (hp : ∀ n, 0 ≤ p.coeff n) (L : ℕ) :
    ∀ n, 0 ≤ (p ^ L).coeff n := by
  induction L with
  | zero => intro n; simp [Polynomial.coeff_one]; split_ifs <;> norm_num
  | succ L ih => simpa only [pow_succ] using nonneg_coeff_mul (p ^ L) p ih hp

/-- Polynomial Picard approximants, with coefficients independent of the
chosen numerical evaluation parameter. -/
def halfProjectionPicardPolynomial (L : ℕ) : ℕ → Polynomial ℝ
  | 0 => 0
  | k + 1 => Polynomial.C ((2 : ℝ) ^ L)⁻¹ * Polynomial.X *
      (1 + halfProjectionPicardPolynomial L k) ^ L

/-- Every coefficient of every Picard approximant is nonnegative. -/
theorem halfProjectionPicardPolynomial_coeff_nonneg (L k n : ℕ) :
    0 ≤ (halfProjectionPicardPolynomial L k).coeff n := by
  induction k generalizing n with
  | zero => simp [halfProjectionPicardPolynomial]
  | succ k ih =>
    apply nonneg_coeff_mul
    · apply nonneg_coeff_mul
      · intro j; simp [Polynomial.coeff_C]; split_ifs <;> positivity
      · intro j; simp [Polynomial.coeff_X]; split_ifs <;> positivity
    · apply nonneg_coeff_pow
      intro j
      rw [Polynomial.coeff_add]
      exact add_nonneg (by simp [Polynomial.coeff_one]; split_ifs <;> positivity) (ih j)

/-- Evaluating the actual polynomial approximant gives exactly the scalar
Picard majorant, with no approximation premise. -/
theorem halfProjectionPicardPolynomial_eval (L k : ℕ) (t : ℝ) :
    (halfProjectionPicardPolynomial L k).eval t = halfProjectionPicard L t k := by
  induction k with
  | zero => simp [halfProjectionPicardPolynomial, halfProjectionPicard]
  | succ k ih =>
    simp only [halfProjectionPicardPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_one, ih,
      halfProjectionPicard, div_eq_mul_inv]
    ring

private theorem polynomial_partial_sum_le_eval (p : Polynomial ℝ)
    (hp : ∀ n, 0 ≤ p.coeff n) (t : ℝ) (ht : 0 ≤ t) (N : ℕ) :
    (∑ n ∈ Finset.range N, p.coeff n * t ^ n) ≤ p.eval t := by
  rw [Polynomial.eval_eq_sum_range' (lt_of_lt_of_le (Nat.lt_succ_self p.natDegree) (le_max_right N (p.natDegree + 1)))]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_max_left N (p.natDegree + 1)))
  intro n _ _
  exact mul_nonneg (hp n) (pow_nonneg ht n)

/-- Every finite coefficient sum is bounded by the same genuine scalar
supersolution. This is the majorant needed for coefficientwise summability. -/
theorem halfProjectionPicardPolynomial_partial_sum_le_supersolution
    (L k N : ℕ) (t : ℝ) (ht : 0 ≤ t) (r : ℝ) (hr : 0 ≤ r)
    (hsuper : (t / (2 : ℝ) ^ L) * (1 + r) ^ L ≤ r) :
    (∑ n ∈ Finset.range N, (halfProjectionPicardPolynomial L k).coeff n * t ^ n) ≤ r := by
  calc
    _ ≤ (halfProjectionPicardPolynomial L k).eval t :=
      polynomial_partial_sum_le_eval _ (halfProjectionPicardPolynomial_coeff_nonneg L k) t ht N
    _ = halfProjectionPicard L t k := halfProjectionPicardPolynomial_eval L k t
    _ ≤ r := halfProjectionPicard_le_supersolution L t ht r hr hsuper k
end FreeProbability

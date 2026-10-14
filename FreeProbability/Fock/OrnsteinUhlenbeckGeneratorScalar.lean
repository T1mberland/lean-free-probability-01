import FreeProbability.Fock.OrnsteinUhlenbeckNumberResolventPositive
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Scalar right-sided difference quotients and the genuine summable generator bound. -/
noncomputable section
open scoped Classical Topology
open Filter
namespace FreeProbability.Fock

/-- Error after adding the expected positive number coefficient to the OU difference quotient. -/
def ouGeneratorScalarError (n : ℕ) (t : ℝ) : ℝ :=
  (Real.exp (-t) ^ n - 1) / t + (n : ℝ)

/-- The actual scalar generator coefficient is -n at time zero. -/
theorem ouGenerator_scalar_hasDerivAt (n : ℕ) :
    HasDerivAt (fun t : ℝ => Real.exp (-t) ^ n) (-(n : ℝ)) 0 := by
  have he : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-1) 0 := by
    simpa [Function.comp_def] using (Real.hasDerivAt_exp (-(0 : ℝ))).comp 0 ((hasDerivAt_id (0 : ℝ)).neg)
  simpa using he.fun_pow n

 theorem ouGeneratorScalarError_tendsto (n : ℕ) :
    Tendsto (ouGeneratorScalarError n) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hq := (ouGenerator_scalar_hasDerivAt n).tendsto_slope_zero_right
  have he := hq.add (tendsto_const_nhds (x := (n : ℝ)))
  unfold ouGeneratorScalarError
  simpa [div_eq_mul_inv, mul_comm] using he

/-- The genuine quotient error is between zero and n at every positive time. -/
theorem ouGeneratorScalarError_bounds (n : ℕ) (t : ℝ) (ht : 0 < t) :
    0 ≤ ouGeneratorScalarError n t ∧ ouGeneratorScalarError n t ≤ (n : ℝ) := by
  have hu : Real.exp (-t) ^ n ≤ 1 :=
    pow_le_one₀ (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht.le))
  have hl := Real.add_one_le_exp ((n : ℝ) * (-t))
  rw [Real.exp_nat_mul] at hl
  have hq : -(n : ℝ) ≤ (Real.exp (-t) ^ n - 1) / t :=
    (le_div_iff₀ ht).mpr (by nlinarith [hl])
  have hq' : (Real.exp (-t) ^ n - 1) / t ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) ht.le
  unfold ouGeneratorScalarError
  constructor <;> linarith

 theorem abs_ouGeneratorScalarError_le (n : ℕ) (t : ℝ) (ht : 0 < t) :
    |ouGeneratorScalarError n t| ≤ (n : ℝ) := by
  rw [abs_of_nonneg (ouGeneratorScalarError_bounds n t ht).1]
  exact (ouGeneratorScalarError_bounds n t ht).2

end FreeProbability.Fock

import FreeProbability.Fock.OrnsteinUhlenbeckGeneratorScalar
import Mathlib.Analysis.Normed.Group.Tannery

/-! Actual completed-Fock generator error and a strong right-sided zero limit on the true domain. -/
noncomputable section
open scoped Classical InnerProductSpace ENNReal Topology
open Filter
namespace FreeProbability.Fock

 theorem abs_ouGeneratorScalarError_max_le (n : ℕ) (t : ℝ) :
    |ouGeneratorScalarError n (max t 0)| ≤ (n : ℝ) := by
  by_cases ht : 0 < t
  · rw [max_eq_left ht.le]
    exact abs_ouGeneratorScalarError_le n t ht
  · rw [max_eq_right (not_lt.mp ht)]
    simp [ouGeneratorScalarError]

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual weighted quotient-error vector, extended to nonpositive times by its time-zero value. -/
def ouGeneratorError (f : numberOperatorDomain H) (t : ℝ) : TensorFullFock H :=
  ⟨fun n => (ouGeneratorScalarError n (max t 0) : ℂ) • (f : TensorFullFock H) n,
    (lp.memℓp (numberOperator H f)).mono' (by
      intro n
      rw [norm_smul, numberOperator_degree, norm_smul, Complex.norm_natCast,
        Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (abs_ouGeneratorScalarError_max_le n t) (norm_nonneg _))⟩

@[simp] theorem ouGeneratorError_degree (f : numberOperatorDomain H) (t : ℝ) (n : ℕ) :
    ouGeneratorError H f t n = (ouGeneratorScalarError n (max t 0) : ℂ) • (f : TensorFullFock H) n := rfl

 theorem norm_ouGeneratorError_degree_le (f : numberOperatorDomain H) (t : ℝ) (n : ℕ) :
    ‖ouGeneratorError H f t n‖ ≤ ‖numberOperator H f n‖ := by
  rw [ouGeneratorError_degree, norm_smul, numberOperator_degree, norm_smul,
    Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (abs_ouGeneratorScalarError_max_le n t) (norm_nonneg _)

 theorem ouGeneratorError_degree_tendsto (f : numberOperatorDomain H) (n : ℕ) :
    Tendsto (fun t => ouGeneratorError H f t n) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have ht : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hs : Tendsto (fun t => ouGeneratorScalarError n (max t 0)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    (ouGeneratorScalarError_tendsto n).congr' (ht.mono (fun t h => by simp only [max_eq_left h.le]))
  have hc := (Complex.continuous_ofReal.tendsto 0).comp hs
  simpa only [ouGeneratorError_degree, Complex.ofReal_zero, zero_smul, Function.comp_def] using
    hc.smul (tendsto_const_nhds (x := (f : TensorFullFock H) n))

/-- The genuine completed Hilbert norm limit uses the actual weighted-domain summable bound. -/
theorem ouGeneratorError_tendsto (f : numberOperatorDomain H) :
    Tendsto (ouGeneratorError H f) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hs : Summable (fun n => ‖numberOperator H f n‖ ^ 2) := by
    simpa using (lp.memℓp (numberOperator H f)).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have hcoord : ∀ n : ℕ,
      Tendsto (fun t => ‖ouGeneratorError H f t n‖ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    intro n
    simpa using (ouGeneratorError_degree_tendsto H f n).norm.pow 2
  have hb : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), ∀ n : ℕ,
      ‖‖ouGeneratorError H f t n‖ ^ 2‖ ≤ ‖numberOperator H f n‖ ^ 2 := by
    exact Eventually.of_forall (fun t n => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_ouGeneratorError_degree_le H f t n) 2)
  have hsum := tendsto_tsum_of_dominated_convergence hs hcoord hb
  have heq : ∀ t : ℝ, ‖ouGeneratorError H f t‖ ^ 2 = ∑' n, ‖ouGeneratorError H f t n‖ ^ 2 := by
    intro t
    simpa using lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (ouGeneratorError H f t)
  have hsq : Tendsto (fun t => ‖ouGeneratorError H f t‖ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [← heq, tsum_zero] using hsum
  have hroot := (Real.continuous_sqrt.tendsto 0).comp hsq
  have hn : Tendsto (fun t => ‖ouGeneratorError H f t‖) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hroot
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hn

end FreeProbability.Fock

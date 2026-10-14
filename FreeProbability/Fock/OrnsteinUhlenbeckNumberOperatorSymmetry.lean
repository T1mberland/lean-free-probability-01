import FreeProbability.Fock.OrnsteinUhlenbeckNumberOperatorDomain

/-! Dense genuine operator domain and symmetric positive number-operator quadratic form.
Symmetry on this specified domain is not asserted to establish unbounded self-adjointness. -/
noncomputable section
open scoped Classical InnerProductSpace ENNReal ComplexOrder
namespace FreeProbability.Fock
variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual weighted-ℓ2 operator domain is dense in the whole complete Fock space. -/
theorem numberOperatorDomain_dense : Dense (numberOperatorDomain H : Set (TensorFullFock H)) := by
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro f
  have hc := (numberOperatorDomain H).isClosed_topologicalClosure
  have hs : ∀ S : Finset ℕ, (∑ n ∈ S, lp.single 2 n (f n)) ∈ (numberOperatorDomain H).topologicalClosure := by
    intro S
    apply Submodule.sum_mem
    intro n _
    exact (numberOperatorDomain H).le_topologicalClosure (single_mem_numberOperatorDomain H n (f n))
  exact hc.mem_of_tendsto (lp.hasSum_single (ENNReal.ofNat_ne_top (n := 2)) f)
    (Filter.Eventually.of_forall hs)

/-- True symmetry of the actual domain-restricted number operator. -/
theorem numberOperator_inner_symmetric (f g : numberOperatorDomain H) :
    inner ℂ (numberOperator H f) (g : TensorFullFock H) =
      inner ℂ (f : TensorFullFock H) (numberOperator H g) := by
  simp only [lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp only [numberOperator_degree, inner_smul_left, inner_smul_right, map_natCast]

/-- Actual nonnegative quadratic form of the number operator on its true operator domain. -/
theorem numberOperator_quadratic_nonneg (f : numberOperatorDomain H) :
    0 ≤ inner ℂ (f : TensorFullFock H) (numberOperator H f) := by
  rw [lp.inner_eq_tsum]
  apply tsum_nonneg
  intro n
  rw [numberOperator_degree, inner_smul_right, inner_self_eq_norm_sq_to_K]
  change 0 ≤ (n : ℂ) * (‖(f : TensorFullFock H) n‖ : ℂ) ^ 2
  apply Complex.nonneg_iff.mpr
  constructor
  · simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    positivity
  · simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
      ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, add_zero]

end FreeProbability.Fock

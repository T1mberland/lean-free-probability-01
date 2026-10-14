import FreeProbability.Fock.OrnsteinUhlenbeckNumberOperatorDamping

/-! Actual contractive inverse weights for the shifted Fock number operator. -/
noncomputable section
open scoped Classical InnerProductSpace ENNReal
namespace FreeProbability.Fock

/-- The genuine scalar weight in completed tensor degree n. -/
def numberResolventWeight (n : ℕ) : ℂ := (((n : ℝ) + 1)⁻¹ : ℝ)

 theorem norm_numberResolventWeight_le_one (n : ℕ) : ‖numberResolventWeight n‖ ≤ 1 := by
  rw [numberResolventWeight, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (by positivity))]
  simpa only [one_div, inv_one] using
    (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith : (1 : ℝ) ≤ (n : ℝ) + 1))

/-- Weighted image coefficients are uniformly bounded as well: this is the actual domain bound. -/
theorem norm_degree_mul_numberResolventWeight_le_one (n : ℕ) :
    ‖(n : ℂ) * numberResolventWeight n‖ ≤ 1 := by
  rw [norm_mul, Complex.norm_natCast, numberResolventWeight, Complex.norm_real,
    Real.norm_of_nonneg (inv_nonneg.mpr (by positivity))]
  calc
    (n : ℝ) * ((n : ℝ) + 1)⁻¹ ≤ ((n : ℝ) + 1) * ((n : ℝ) + 1)⁻¹ := by
      gcongr
      norm_num
    _ = 1 := mul_inv_cancel₀ (by positivity)

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Actual resolvent weighting as a linear map on every completed Fock vector. -/
def numberResolventLinear : TensorFullFock H →ₗ[ℂ] TensorFullFock H where
  toFun f := ⟨fun n => numberResolventWeight n • f n, (lp.memℓp f).mono' (by
    intro n
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_right (norm_numberResolventWeight_le_one n) (norm_nonneg _)).trans_eq
      (one_mul _))⟩
  map_add' := by
    intro f g
    apply lp.ext
    funext n
    exact smul_add _ _ _
  map_smul' := by
    intro c f
    apply lp.ext
    funext n
    exact smul_comm _ _ _

 theorem norm_numberResolventLinear_le (f : TensorFullFock H) : ‖numberResolventLinear H f‖ ≤ ‖f‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro n
  change ‖numberResolventWeight n • f n‖ ≤ ‖f n‖
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_right (norm_numberResolventWeight_le_one n) (norm_nonneg _)).trans_eq
    (one_mul _)

/-- Genuine bounded shift inverse on the entire complete tensor Fock space. -/
def numberResolvent : TensorFullFock H →L[ℂ] TensorFullFock H :=
  (numberResolventLinear H).mkContinuous 1 (by
    intro f
    simpa only [one_mul] using norm_numberResolventLinear_le H f)

@[simp] theorem numberResolvent_degree (f : TensorFullFock H) (n : ℕ) :
    numberResolvent H f n = numberResolventWeight n • f n := rfl

 theorem norm_numberResolvent_apply_le (f : TensorFullFock H) : ‖numberResolvent H f‖ ≤ ‖f‖ :=
  norm_numberResolventLinear_le H f

 theorem norm_numberResolvent_le : ‖numberResolvent H‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using norm_numberResolvent_apply_le H f

end FreeProbability.Fock

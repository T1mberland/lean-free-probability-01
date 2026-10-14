import FreeProbability.Fock.OrnsteinUhlenbeckSemigroupLaws

/-! # Genuine degree damping on the complete tensor Hilbert direct sum -/
noncomputable section
open scoped Classical ENNReal
namespace FreeProbability.Fock
variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual scalar multiplier on completed tensor degree n at time t. -/
def degreeWeight (t : ℝ) (n : ℕ) : ℂ := (Real.exp (-t) : ℂ) ^ n

theorem norm_degreeWeight_le_one (t : ℝ) (ht : 0 ≤ t) (n : ℕ) : ‖degreeWeight t n‖ ≤ 1 := by
  rw [degreeWeight, norm_pow, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact pow_le_one₀ (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht))

/-- Coordinatewise damping as an actual linear map on all square-summable tensor vectors. -/
def degreeDampingLinear (t : ℝ) (ht : 0 ≤ t) : TensorFullFock H →ₗ[ℂ] TensorFullFock H where
  toFun f := ⟨fun n => degreeWeight t n • f n, (lp.memℓp f).mono' (by
    intro n
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_right (norm_degreeWeight_le_one t ht n) (norm_nonneg (f n))).trans
      (one_mul _).le)⟩
  map_add' f g := by ext n; simp [smul_add]; rfl
  map_smul' c f := by ext n; simp [smul_smul, mul_comm]

@[simp] theorem degreeDampingLinear_degree (t : ℝ) (ht : 0 ≤ t)
    (f : TensorFullFock H) (n : ℕ) : degreeDampingLinear H t ht f n = degreeWeight t n • f n := rfl

/-- True Hilbert norm contraction, on infinite sums as well as finite tensors. -/
theorem norm_degreeDampingLinear_le (t : ℝ) (ht : 0 ≤ t) (f : TensorFullFock H) :
    ‖degreeDampingLinear H t ht f‖ ≤ ‖f‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro n
  change ‖degreeWeight t n • f n‖ ≤ ‖f n‖
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_right (norm_degreeWeight_le_one t ht n) (norm_nonneg (f n))).trans
    (one_mul _).le

/-- Genuine bounded degree damping on the complete tensor Fock Hilbert space. -/
def degreeDamping (t : ℝ) (ht : 0 ≤ t) : TensorFullFock H →L[ℂ] TensorFullFock H :=
  (degreeDampingLinear H t ht).mkContinuous 1 (by
    intro f
    simpa only [one_mul] using norm_degreeDampingLinear_le H t ht f)

@[simp] theorem degreeDamping_degree (t : ℝ) (ht : 0 ≤ t) (f : TensorFullFock H) (n : ℕ) :
    degreeDamping H t ht f n = degreeWeight t n • f n := rfl

@[simp] theorem degreeDamping_single (t : ℝ) (ht : 0 ≤ t) (n : ℕ) (f : TensorPower H n) :
    degreeDamping H t ht (lp.single 2 n f) = degreeWeight t n • lp.single 2 n f := by
  apply lp.ext
  funext j
  by_cases hj : j = n
  · subst j; simp [lp.single_apply]
  · simp [lp.single_apply, hj]

@[simp] theorem degreeDamping_vacuum (t : ℝ) (ht : 0 ≤ t) :
    degreeDamping H t ht (tensorVacuum H) = tensorVacuum H := by
  rw [tensorVacuum, degreeDamping_single]
  simp [degreeWeight]

theorem norm_degreeDamping_le (t : ℝ) (ht : 0 ≤ t) (f : TensorFullFock H) :
    ‖degreeDamping H t ht f‖ ≤ ‖f‖ := norm_degreeDampingLinear_le H t ht f

/-- Exact zero-time identity on all of the actual Hilbert direct sum. -/
@[simp] theorem degreeDamping_zero : degreeDamping H 0 (le_refl 0) = ContinuousLinearMap.id ℂ (TensorFullFock H) := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext n
  simp [degreeDamping_degree, degreeWeight]

/-- Actual Hilbert-space semigroup law, on every square-summable tensor vector. -/
theorem degreeDamping_add (t u : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    (degreeDamping H t ht).comp (degreeDamping H u hu) =
      degreeDamping H (t + u) (add_nonneg ht hu) := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext n
  change degreeWeight t n • (degreeWeight u n • f n) = degreeWeight (t + u) n • f n
  rw [smul_smul]
  have hw : degreeWeight t n * degreeWeight u n = degreeWeight (t + u) n := by
    simp only [degreeWeight, neg_add, Real.exp_add, Complex.ofReal_mul, mul_pow]
  rw [hw]

end FreeProbability.Fock

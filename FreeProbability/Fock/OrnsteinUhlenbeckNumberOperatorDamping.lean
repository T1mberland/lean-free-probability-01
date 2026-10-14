import FreeProbability.Fock.OrnsteinUhlenbeckNumberOperatorSymmetry

/-! Genuine invariance of the weighted operator domain under actual degree damping. -/
noncomputable section
open scoped Classical InnerProductSpace ENNReal
namespace FreeProbability.Fock
variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Actual degree damping preserves the exact weighted-ℓ2 operator domain. -/
theorem degreeDamping_mem_numberOperatorDomain (t : ℝ) (ht : 0 ≤ t) (f : numberOperatorDomain H) :
    degreeDamping H t ht (f : TensorFullFock H) ∈ numberOperatorDomain H := by
  change Memℓp (fun n : ℕ => (n : ℂ) • degreeDamping H t ht (f : TensorFullFock H) n) 2
  apply (lp.memℓp (numberOperator H f)).mono'
  intro n
  rw [degreeDamping_degree, numberOperator_degree,
    smul_comm (n : ℂ) (degreeWeight t n), norm_smul]
  exact (mul_le_mul_of_nonneg_right (norm_degreeWeight_le_one t ht n) (norm_nonneg _)).trans_eq
    (one_mul _)

/-- The genuine degree semigroup restricted to its invariant number-operator domain. -/
def numberOperatorDamping (t : ℝ) (ht : 0 ≤ t) : numberOperatorDomain H →ₗ[ℂ] numberOperatorDomain H where
  toFun f := ⟨degreeDamping H t ht (f : TensorFullFock H), degreeDamping_mem_numberOperatorDomain H t ht f⟩
  map_add' f g := by
    apply Subtype.ext
    exact map_add (degreeDamping H t ht) (f : TensorFullFock H) (g : TensorFullFock H)
  map_smul' c f := by
    apply Subtype.ext
    exact map_smul (degreeDamping H t ht) c (f : TensorFullFock H)

@[simp] theorem numberOperatorDamping_coe (t : ℝ) (ht : 0 ≤ t) (f : numberOperatorDomain H) :
    (numberOperatorDamping H t ht f : TensorFullFock H) = degreeDamping H t ht (f : TensorFullFock H) := rfl

/-- The actual domain-restricted number operator commutes with actual degree damping. -/
theorem numberOperator_damping (t : ℝ) (ht : 0 ≤ t) (f : numberOperatorDomain H) :
    numberOperator H (numberOperatorDamping H t ht f) = degreeDamping H t ht (numberOperator H f) := by
  apply lp.ext
  funext n
  rw [numberOperator_degree, numberOperatorDamping_coe, degreeDamping_degree,
    degreeDamping_degree, numberOperator_degree]
  exact smul_comm _ _ _

 theorem norm_numberOperator_damping_le (t : ℝ) (ht : 0 ≤ t) (f : numberOperatorDomain H) :
    ‖numberOperator H (numberOperatorDamping H t ht f)‖ ≤ ‖numberOperator H f‖ := by
  rw [numberOperator_damping]
  exact norm_degreeDamping_le H t ht _

/-- Exact semigroup identity on the genuine invariant operator domain. -/
theorem numberOperatorDamping_add (t u : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    (numberOperatorDamping H t ht).comp (numberOperatorDamping H u hu) =
      numberOperatorDamping H (t + u) (add_nonneg ht hu) := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  exact DFunLike.congr_fun (degreeDamping_add H t u ht hu) (f : TensorFullFock H)

end FreeProbability.Fock

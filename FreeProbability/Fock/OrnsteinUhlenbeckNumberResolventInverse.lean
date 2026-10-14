import FreeProbability.Fock.OrnsteinUhlenbeckNumberResolvent

/-! Actual two-sided shift inverse with its exact number-operator domain. -/
noncomputable section
open scoped Classical InnerProductSpace ENNReal
namespace FreeProbability.Fock

 theorem numberResolventWeight_shift (n : ℕ) : ((n : ℂ) + 1) * numberResolventWeight n = 1 := by
  unfold numberResolventWeight
  exact_mod_cast (mul_inv_cancel₀ (by positivity : (n : ℝ) + 1 ≠ 0))

 theorem numberResolventWeight_degree_add (n : ℕ) :
    (n : ℂ) * numberResolventWeight n + numberResolventWeight n = 1 := by
  calc
    _ = ((n : ℂ) + 1) * numberResolventWeight n := by ring
    _ = 1 := numberResolventWeight_shift n

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every ambient vector is sent into the exact weighted-square-summability operator domain. -/
theorem numberResolvent_mem_domain (f : TensorFullFock H) :
    numberResolvent H f ∈ numberOperatorDomain H := by
  change Memℓp (fun n : ℕ => (n : ℂ) • numberResolvent H f n) 2
  apply (lp.memℓp f).mono'
  intro n
  rw [numberResolvent_degree, smul_smul, norm_smul]
  exact (mul_le_mul_of_nonneg_right (norm_degree_mul_numberResolventWeight_le_one n)
    (norm_nonneg _)).trans_eq (one_mul _)

/-- The actual shift N+1 on its genuine operator domain. -/
def numberShift : numberOperatorDomain H →ₗ[ℂ] TensorFullFock H :=
  numberOperator H + (numberOperatorDomain H).subtype

/-- Actual resolvent with its proved domain-valued output. -/
def numberResolventDomain : TensorFullFock H →ₗ[ℂ] numberOperatorDomain H where
  toFun f := ⟨numberResolvent H f, numberResolvent_mem_domain H f⟩
  map_add' f g := by apply Subtype.ext; exact map_add (numberResolvent H) f g
  map_smul' c f := by apply Subtype.ext; exact map_smul (numberResolvent H) c f

/-- The genuine shift composed with the domain-valued resolvent fixes EVERY ambient Fock vector. -/
theorem numberShift_numberResolvent (f : TensorFullFock H) :
    numberShift H (numberResolventDomain H f) = f := by
  apply lp.ext
  funext n
  change (n : ℂ) • numberResolvent H f n + numberResolvent H f n = f n
  rw [numberResolvent_degree, smul_smul, ← add_smul, numberResolventWeight_degree_add, one_smul]

/-- The actual resolvent is also the left inverse on the whole genuine number domain. -/
theorem numberResolvent_numberShift (f : numberOperatorDomain H) :
    numberResolventDomain H (numberShift H f) = f := by
  apply Subtype.ext
  apply lp.ext
  funext n
  change numberResolvent H (numberShift H f) n = (f : TensorFullFock H) n
  rw [numberResolvent_degree]
  change numberResolventWeight n •
    ((n : ℂ) • (f : TensorFullFock H) n + (f : TensorFullFock H) n) = _
  rw [smul_add, smul_smul, ← add_smul]
  have hh : numberResolventWeight n * (n : ℂ) + numberResolventWeight n = 1 := by
    rw [mul_comm]
    exact numberResolventWeight_degree_add n
  rw [hh, one_smul]

/-- The actual shift on its exact weighted domain is bijective onto complete Fock space. -/
theorem numberShift_bijective : Function.Bijective (numberShift H) :=
  ⟨Function.LeftInverse.injective (numberResolvent_numberShift H),
    Function.RightInverse.surjective (numberShift_numberResolvent H)⟩

end FreeProbability.Fock

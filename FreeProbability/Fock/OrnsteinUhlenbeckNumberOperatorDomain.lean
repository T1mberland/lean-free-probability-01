import FreeProbability.Fock.OrnsteinUhlenbeckL2Damping

/-! The genuine weighted-square-summability operator domain of the Fock number operator.
The domain-restricted linear operator takes values in the ambient complete Fock space.
No continuity on the ambient space or identification with the quadratic-form domain is assumed. -/
noncomputable section
open scoped Classical InnerProductSpace ENNReal
namespace FreeProbability.Fock
variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Exactly the vectors for which multiplying tensor degree n by n remains square summable. -/
def numberOperatorDomain : Submodule ℂ (TensorFullFock H) where
  carrier := {f | Memℓp (fun n : ℕ => (n : ℂ) • f n) 2}
  zero_mem' := by
    change Memℓp (fun n : ℕ => (n : ℂ) • (0 : TensorFullFock H) n) 2
    convert lp.memℓp (0 : TensorFullFock H) using 1
    funext n
    exact smul_zero (n : ℂ)
  add_mem' := by
    intro f g hf hg
    change Memℓp (fun n : ℕ => (n : ℂ) • (f n + g n)) 2
    convert hf.add hg using 1
    funext n
    exact smul_add _ _ _
  smul_mem' := by
    intro c f hf
    change Memℓp (fun n : ℕ => (n : ℂ) • (c • f n)) 2
    convert hf.const_smul c using 1
    funext n
    exact smul_comm (n : ℂ) c (f n)

@[simp] theorem mem_numberOperatorDomain (f : TensorFullFock H) :
    f ∈ numberOperatorDomain H ↔ Memℓp (fun n : ℕ => (n : ℂ) • f n) 2 := Iff.rfl

/-- The actual number operator on its true operator domain. -/
def numberOperator : numberOperatorDomain H →ₗ[ℂ] TensorFullFock H where
  toFun f := ⟨fun n : ℕ => (n : ℂ) • (f : TensorFullFock H) n, f.property⟩
  map_add' := by
    intro f g
    apply lp.ext
    funext n
    change (n : ℂ) • ((f : TensorFullFock H) n + (g : TensorFullFock H) n) = _
    exact smul_add _ _ _
  map_smul' := by
    intro c f
    apply lp.ext
    funext n
    change (n : ℂ) • (c • (f : TensorFullFock H) n) = c • ((n : ℂ) • (f : TensorFullFock H) n)
    exact smul_comm _ _ _

@[simp] theorem numberOperator_degree (f : numberOperatorDomain H) (n : ℕ) :
    numberOperator H f n = (n : ℂ) • (f : TensorFullFock H) n := rfl

/-- Every pure completed tensor degree belongs to the genuine operator domain. -/
theorem single_mem_numberOperatorDomain (n : ℕ) (f : TensorPower H n) :
    lp.single 2 n f ∈ numberOperatorDomain H := by
  change Memℓp (fun k : ℕ => (k : ℂ) • (lp.single 2 n f : TensorFullFock H) k) 2
  have he : (fun k : ℕ => (k : ℂ) • (lp.single 2 n f : TensorFullFock H) k) =
      ⇑(lp.single 2 n ((n : ℂ) • f) : TensorFullFock H) := by
    funext k
    by_cases hk : k = n
    · subst k
      simp only [lp.single_apply_self]
    · simp only [lp.single_apply_ne _ _ _ hk, smul_zero]
  rw [he]
  exact lp.memℓp _

/-- The actual number operator acts by n on its actual completed tensor degree. -/
theorem numberOperator_single (n : ℕ) (f : TensorPower H n) :
    numberOperator H ⟨lp.single 2 n f, single_mem_numberOperatorDomain H n f⟩ =
      lp.single 2 n ((n : ℂ) • f) := by
  apply lp.ext
  funext k
  by_cases hk : k = n
  · subst k
    simp only [numberOperator_degree, lp.single_apply_self]
  · simp only [numberOperator_degree, lp.single_apply_ne _ _ _ hk, smul_zero]

end FreeProbability.Fock

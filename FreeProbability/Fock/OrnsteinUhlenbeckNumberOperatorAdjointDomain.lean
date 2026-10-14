import FreeProbability.Fock.OrnsteinUhlenbeckNumberOperatorSymmetry

/-! Exact weak-adjoint graph of the actual number operator, including its full operator domain.
This goes beyond symmetry: every possible weak-adjoint vector lies in the genuine weighted domain. -/
noncomputable section
open scoped Classical InnerProductSpace ENNReal
namespace FreeProbability.Fock
variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Testing the weak adjoint identity in every actual completed tensor grade determines all coordinates. -/
theorem numberOperator_adjoint_coordinates (y z : TensorFullFock H)
    (h : ∀ f : numberOperatorDomain H,
      inner ℂ (numberOperator H f) y = inner ℂ (f : TensorFullFock H) z) :
    ∀ n : ℕ, z n = (n : ℂ) • y n := by
  intro n
  apply ext_inner_left ℂ
  intro v
  have hv := h ⟨lp.single 2 n v, single_mem_numberOperatorDomain H n v⟩
  rw [numberOperator_single, lp.inner_single_left, lp.inner_single_left] at hv
  rw [inner_smul_left, map_natCast] at hv
  rw [inner_smul_right]
  exact hv.symm

/-- Every weak-adjoint vector belongs to the actual operator domain; no larger domain is assumed. -/
theorem numberOperator_adjoint_mem_domain (y z : TensorFullFock H)
    (h : ∀ f : numberOperatorDomain H,
      inner ℂ (numberOperator H f) y = inner ℂ (f : TensorFullFock H) z) :
    y ∈ numberOperatorDomain H := by
  change Memℓp (fun n : ℕ => (n : ℂ) • y n) 2
  convert lp.memℓp z using 1
  funext n
  exact (numberOperator_adjoint_coordinates H y z h n).symm

/-- Exact equality of the full weak-adjoint graph and the actual number-operator graph. -/
theorem numberOperator_adjoint_graph_iff (y z : TensorFullFock H) :
    (∀ f : numberOperatorDomain H,
      inner ℂ (numberOperator H f) y = inner ℂ (f : TensorFullFock H) z) ↔
    ∃ g : numberOperatorDomain H, (g : TensorFullFock H) = y ∧ numberOperator H g = z := by
  constructor
  · intro h
    refine ⟨⟨y, numberOperator_adjoint_mem_domain H y z h⟩, rfl, ?_⟩
    apply lp.ext
    funext n
    exact (numberOperator_adjoint_coordinates H y z h n).symm
  · rintro ⟨g, rfl, rfl⟩ f
    exact numberOperator_inner_symmetric H f g

end FreeProbability.Fock

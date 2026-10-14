import FreeProbability.Fock.OrnsteinUhlenbeckNumberOperatorAdjointDomain

/-! The actual number-operator graph is closed in the product of completed Fock spaces. -/
noncomputable section
open scoped Classical InnerProductSpace
namespace FreeProbability.Fock
variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The genuine graph with the exact weighted operator domain. -/
def numberOperatorGraph : Set (TensorFullFock H × TensorFullFock H) :=
  {p | ∃ f : numberOperatorDomain H, (f : TensorFullFock H) = p.1 ∧ numberOperator H f = p.2}

/-- The actual graph is the intersection of its genuine weak-adjoint coefficient equations. -/
theorem numberOperatorGraph_eq_inter : numberOperatorGraph H =
    ⋂ f : numberOperatorDomain H,
      {p : TensorFullFock H × TensorFullFock H |
        inner ℂ (numberOperator H f) p.1 = inner ℂ (f : TensorFullFock H) p.2} := by
  ext p
  simp only [numberOperatorGraph, Set.mem_ofPred_eq, Set.mem_iInter]
  exact (numberOperator_adjoint_graph_iff H p.1 p.2).symm

/-- Norm limits of actual graph points remain in the exact number-operator graph. -/
theorem isClosed_numberOperatorGraph : IsClosed (numberOperatorGraph H) := by
  rw [numberOperatorGraph_eq_inter]
  apply isClosed_iInter
  intro f
  exact isClosed_eq (continuous_const.inner continuous_fst) (continuous_const.inner continuous_snd)

/-- A convergent graph net has its actual limit in the weighted operator domain and graph. -/
theorem numberOperator_closed_limit {α : Type*} {l : Filter α} [l.NeBot]
    (f : α → numberOperatorDomain H) (y z : TensorFullFock H)
    (hy : Filter.Tendsto (fun a => (f a : TensorFullFock H)) l (nhds y))
    (hz : Filter.Tendsto (fun a => numberOperator H (f a)) l (nhds z)) :
    ∃ g : numberOperatorDomain H, (g : TensorFullFock H) = y ∧ numberOperator H g = z := by
  apply (isClosed_numberOperatorGraph H).mem_of_tendsto (hy.prodMk_nhds hz)
  exact Filter.Eventually.of_forall (fun a => ⟨f a, rfl, rfl⟩)

end FreeProbability.Fock

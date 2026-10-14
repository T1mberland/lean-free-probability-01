import FreeProbability.Fock.OrnsteinUhlenbeckGeneratorDomain

/-! Standard derivative-within-set interface for the genuine right strong OU generator. -/
noncomputable section
open scoped Classical InnerProductSpace Topology
namespace FreeProbability.Fock
variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem ouGenerator_punctured_nonnegative :
    Set.Ici (0 : ℝ) \ {0} = Set.Ioi 0 := by
  ext t
  simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_singleton_iff, Set.mem_Ioi]
  constructor
  · intro h
    exact lt_of_le_of_ne h.1 (by intro he; exact h.2 he.symm)
  · intro h
    exact ⟨h.le, ne_of_gt h⟩

/-- The usual real-variable slope agrees with the actual complex-scaled quotient on this Hilbert space. -/
theorem ouGenerator_slope_zero (f : TensorFullFock H) :
    slope (fun t : ℝ => ouGeneratorDamping H t f) 0 = ouGeneratorQuotient H f := by
  funext t
  have hz : ouGeneratorDamping H 0 f = f := by
    rw [ouGeneratorDamping_nonneg H 0 (le_refl 0), degreeDamping_zero]
    rfl
  rw [slope_def_module, hz, sub_zero]
  unfold ouGeneratorQuotient
  simpa using (IsScalarTower.algebraMap_smul (A := ℂ) (t⁻¹) (ouGeneratorDamping H t f - f)).symm

/-- Standard kernel-verified derivative at zero within nonnegative time, on the full genuine operator domain. -/
theorem ouGenerator_hasDerivWithinAt (f : numberOperatorDomain H) :
    HasDerivWithinAt (fun t : ℝ => ouGeneratorDamping H t (f : TensorFullFock H))
      (-numberOperator H f) (Set.Ici 0) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope, ouGenerator_punctured_nonnegative, ouGenerator_slope_zero]
  exact ouGenerator_right_tendsto H f

/-- Exact standard right derivative graph, including the converse operator-domain characterization. -/
theorem ouGenerator_hasDerivWithinAt_iff (f z : TensorFullFock H) :
    HasDerivWithinAt (fun t : ℝ => ouGeneratorDamping H t f) z (Set.Ici 0) 0 ↔
      ∃ g : numberOperatorDomain H, (g : TensorFullFock H) = f ∧ z = -numberOperator H g := by
  rw [hasDerivWithinAt_iff_tendsto_slope, ouGenerator_punctured_nonnegative, ouGenerator_slope_zero]
  exact ouGenerator_graph_iff H f z

end FreeProbability.Fock

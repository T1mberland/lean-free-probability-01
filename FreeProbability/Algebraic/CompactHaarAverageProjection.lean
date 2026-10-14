import FreeProbability.Algebraic.CompactHaarAverage

/-! # Genuine self-adjoint orthogonal projection from Haar integration -/

noncomputable section
open scoped RealInnerProductSpace
namespace FreeProbability
open MeasureTheory
variable {G E : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
namespace CompactIsometricRepresentation
variable (ρ : CompactIsometricRepresentation G ℝ E)

/-- Integrating a genuine isometric orbit preserves inner products against
fixed vectors. This is derived from the actual Bochner integral. -/
theorem inner_average_of_fixed {w : E} (hw : w ∈ ρ.fixedVectors) (v : E) :
    ⟪w, ρ.average v⟫ = ⟪w, v⟫ := by
  have hint := (innerSL ℝ w).integral_comp_comm (ρ.integrable_orbit v)
  change (∫ g : G, ⟪w, ρ.action g v⟫ ∂CompactHaar.probability G) =
    ⟪w, ρ.average v⟫ at hint
  rw [← hint]
  have he (g : G) : ⟪w, ρ.action g v⟫ = ⟪w, v⟫ := by
    have h := (ρ.action g).inner_map_map w v
    rw [hw g] at h
    exact h
  simp only [he, integral_const, probReal_univ, one_smul]

/-- The actual averaging operator is symmetric for the actual Hilbert inner product. -/
theorem inner_average (v w : E) : ⟪ρ.average v, w⟫ = ⟪v, ρ.average w⟫ := by
  have hv : ρ.average v ∈ ρ.fixedVectors := fun g => ρ.action_average g v
  have hw : ρ.average w ∈ ρ.fixedVectors := fun g => ρ.action_average g w
  calc
    ⟪ρ.average v, w⟫ = ⟪ρ.average v, ρ.average w⟫ :=
      (ρ.inner_average_of_fixed hv w).symm
    _ = ⟪ρ.average w, ρ.average v⟫ := real_inner_comm _ _
    _ = ⟪ρ.average w, v⟫ := ρ.inner_average_of_fixed hw v
    _ = ⟪v, ρ.average w⟫ := real_inner_comm _ _

/-- Genuine self-adjointness of the bounded integral operator. -/
theorem averageCLM_isSelfAdjoint : IsSelfAdjoint ρ.averageCLM := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  exact ρ.inner_average

/-- Genuine idempotency in the continuous operator algebra. -/
theorem averageCLM_isIdempotent : IsIdempotentElem ρ.averageCLM := by
  ext v
  exact ρ.average_idempotent v

/-- Actual averaging is a projection onto the exact group-fixed subspace. -/
theorem averageCLM_isProj : LinearMap.IsProj ρ.fixedVectors ρ.averageCLM.toLinearMap := by
  constructor
  · exact fun v g => ρ.action_average g v
  · exact fun v hv => ρ.average_eq_self hv

/-- The residual is genuinely orthogonal to every invariant vector. -/
theorem sub_average_mem_orthogonal (v : E) : v - ρ.average v ∈ ρ.fixedVectors.orthogonal := by
  rw [Submodule.mem_orthogonal]
  intro w hw
  rw [inner_sub_right, ρ.inner_average_of_fixed hw v, sub_self]

/-- The actual kernel is exactly the orthogonal complement of fixed vectors. -/
theorem ker_averageCLM : LinearMap.ker ρ.averageCLM.toLinearMap = ρ.fixedVectors.orthogonal := by
  ext v
  constructor
  · intro hv
    have he : ρ.average v = 0 := hv
    have h := ρ.sub_average_mem_orthogonal v
    simpa only [he, sub_zero] using h
  · intro hv
    have hav : ρ.average v ∈ ρ.fixedVectors := fun g => ρ.action_average g v
    have hzero : ⟪ρ.average v, v⟫ = 0 := ((Submodule.mem_orthogonal _ _).mp hv) (ρ.average v) hav
    change ρ.average v = 0
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [ρ.inner_average_of_fixed hav v, hzero]

/-- Self-adjointness, idempotency, exact fixed range, and exact orthogonal kernel
all hold for the actual integral operator without invariant-tensor premises. -/
theorem averageCLM_orthogonal_projection :
    IsSelfAdjoint ρ.averageCLM ∧ IsIdempotentElem ρ.averageCLM ∧
      LinearMap.range ρ.averageCLM.toLinearMap = ρ.fixedVectors ∧
      LinearMap.ker ρ.averageCLM.toLinearMap = ρ.fixedVectors.orthogonal :=
  ⟨ρ.averageCLM_isSelfAdjoint, ρ.averageCLM_isIdempotent, ρ.range_averageCLM, ρ.ker_averageCLM⟩
end CompactIsometricRepresentation
end FreeProbability

import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Actual normalized compact Haar averaging of continuous isometric representations -/

noncomputable section
namespace FreeProbability
open MeasureTheory

namespace CompactHaar
variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- The actual Haar measure normalized on the whole compact group. -/
def probability : Measure G := Measure.haarMeasure ⊤

instance : Measure.IsHaarMeasure (probability G) := by unfold probability; infer_instance
instance : IsProbabilityMeasure (probability G) where
  measure_univ := Measure.haarMeasure_self
end CompactHaar

variable {G E : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A genuine isometric group representation with continuous vector orbits.
This includes finite-dimensional unitary and orthogonal representations and
also permits complete infinite-dimensional Hilbert spaces. -/
structure CompactIsometricRepresentation (G 𝕜 E : Type*) [Group G] [TopologicalSpace G]
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] where
  action : G →* (E ≃ₗᵢ[𝕜] E)
  continuous_orbit : ∀ v : E, Continuous (fun g : G => action g v)

namespace CompactIsometricRepresentation
variable (ρ : CompactIsometricRepresentation G ℝ E)

omit [CompleteSpace E] in
/-- Every vector orbit is genuinely Bochner integrable against normalized Haar. -/
theorem integrable_orbit (v : E) :
    Integrable (fun g : G => ρ.action g v) (CompactHaar.probability G) :=
  (ρ.continuous_orbit v).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Actual averaging, defined by a Bochner integral rather than a projection premise. -/
def average (v : E) : E := ∫ g : G, ρ.action g v ∂CompactHaar.probability G

omit [CompleteSpace E] in
theorem average_add (v w : E) : ρ.average (v + w) = ρ.average v + ρ.average w := by
  simp only [average, map_add]
  exact integral_add (ρ.integrable_orbit v) (ρ.integrable_orbit w)

omit [CompleteSpace E] in
theorem average_smul (c : ℝ) (v : E) : ρ.average (c • v) = c • ρ.average v := by
  simp only [average, map_smul]
  exact integral_smul c _

omit [CompleteSpace E] in
/-- Actual averaging has contraction bound one in the genuine Hilbert norm. -/
theorem norm_average_le (v : E) : ‖ρ.average v‖ ≤ ‖v‖ := by
  have h := norm_integral_le_integral_norm (μ := CompactHaar.probability G) (fun g : G => ρ.action g v)
  simpa only [average, LinearIsometryEquiv.norm_map, integral_const,
    probReal_univ, one_smul] using h

/-- The actual integral packaged as a bounded linear operator. -/
def averageCLM : E →L[ℝ] E :=
  (show E →ₗ[ℝ] E from
    { toFun := ρ.average
      map_add' := ρ.average_add
      map_smul' := ρ.average_smul }).mkContinuous 1
      (fun v => by change ‖ρ.average v‖ ≤ 1 * ‖v‖; simpa only [one_mul] using ρ.norm_average_le v)

omit [CompleteSpace E] in
@[simp] theorem averageCLM_apply (v : E) : ρ.averageCLM v = ρ.average v := rfl

omit [CompleteSpace E] in
theorem norm_averageCLM_le : ‖ρ.averageCLM‖ ≤ 1 :=
  ρ.averageCLM.opNorm_le_bound (by norm_num) (fun v => by simpa using ρ.norm_average_le v)

omit [CompleteSpace E] in
/-- The actual averaged vector is fixed by every group element. -/
theorem action_average (g : G) (v : E) : ρ.action g (ρ.average v) = ρ.average v := by
  have h := (ρ.action g).toContinuousLinearEquiv.integral_comp_comm
    (μ := CompactHaar.probability G) (fun h : G => ρ.action h v)
  change (∫ h : G, ρ.action g (ρ.action h v) ∂CompactHaar.probability G) =
    ρ.action g (ρ.average v) at h
  rw [← h]
  change (∫ h : G, ρ.action g (ρ.action h v) ∂CompactHaar.probability G) = _
  have hm (h : G) : ρ.action g (ρ.action h v) = ρ.action (g * h) v := by
    rw [map_mul]
    rfl
  simp_rw [hm]
  exact integral_mul_left_eq_self (fun h : G => ρ.action h v) g

/-- Every fixed vector is preserved by actual averaging. -/
theorem average_eq_self {v : E} (hv : ∀ g : G, ρ.action g v = v) : ρ.average v = v := by
  simp only [average, hv, integral_const, probReal_univ, one_smul]

/-- The exact subspace of group-invariant vectors. -/
def fixedVectors : Submodule ℝ E where
  carrier := {v | ∀ g : G, ρ.action g v = v}
  zero_mem' := by intro g; simp
  add_mem' := by
    intro v w hv hw g
    exact (ρ.action g).map_add v w |>.trans (congrArg₂ (· + ·) (hv g) (hw g))
  smul_mem' := by
    intro c v hv g
    exact ((ρ.action g).map_smul c v).trans (congrArg (c • ·) (hv g))

omit [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [CompleteSpace E] in
@[simp] theorem mem_fixedVectors (v : E) : v ∈ ρ.fixedVectors ↔ ∀ g : G, ρ.action g v = v := Iff.rfl

/-- Actual averaging is idempotent. -/
theorem average_idempotent (v : E) : ρ.average (ρ.average v) = ρ.average v :=
  ρ.average_eq_self (fun g => ρ.action_average g v)

/-- Its actual linear range is EXACTLY the invariant-vector subspace. -/
theorem range_averageCLM : LinearMap.range ρ.averageCLM.toLinearMap = ρ.fixedVectors := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    exact fun g => ρ.action_average g w
  · intro hv
    exact ⟨v, ρ.average_eq_self hv⟩
end CompactIsometricRepresentation
end FreeProbability

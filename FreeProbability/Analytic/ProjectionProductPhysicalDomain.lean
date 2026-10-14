import FreeProbability.Analytic.ProjectionProductPhysicalUniqueness

/-! # The physical domain in the original exterior coordinate -/

noncomputable section
namespace FreeProbability

/-- For lengths above two, normalization gives the finite physical interval. -/
theorem halfProjection_physical_interval_iff (L : ℕ) (hL : 3 ≤ L)
    (w : ℝ) (hw : 0 < w) :
    w / (1 + w) < halfProjectionCriticalQ L ↔ w < 1 / ((L : ℝ) - 2) := by
  have hLr : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have h1 : 0 < 1 + w := by linarith
  have hL1 : 0 < (L : ℝ) - 1 := by linarith
  have hL2 : 0 < (L : ℝ) - 2 := by linarith
  unfold halfProjectionCriticalQ
  rw [div_lt_div_iff₀ h1 hL1, lt_div_iff₀ hL2]
  constructor <;> intro h <;> nlinarith

/-- At length two every positive exterior coordinate belongs to the physical
normalized interval; no finite original-coordinate critical point exists. -/
theorem halfProjection_physical_interval_two (w : ℝ) (hw : 0 < w) :
    w / (1 + w) < halfProjectionCriticalQ 2 := by
  norm_num [halfProjectionCriticalQ]
  exact (div_lt_one (by linarith)).mpr (by linarith)

/-- A single predicate preserves both the length-two boundary and the finite
interval for larger lengths. -/
def halfProjectionPhysicalDomain (L : ℕ) (w : ℝ) : Prop :=
  0 < w ∧ (L = 2 ∨ w < 1 / ((L : ℝ) - 2))

theorem halfProjectionPhysicalDomain_iff (L : ℕ) (hL : 2 ≤ L) (w : ℝ) :
    halfProjectionPhysicalDomain L w ↔ 0 < w ∧ w / (1 + w) < halfProjectionCriticalQ L := by
  unfold halfProjectionPhysicalDomain
  by_cases he : L = 2
  · subst L
    simp only [true_or, and_true]
    exact ⟨fun hw => ⟨hw, halfProjection_physical_interval_two w hw⟩, And.left⟩
  · have hL3 : 3 ≤ L := by omega
    simp only [he, false_or]
    constructor
    · rintro ⟨hw, hc⟩
      exact ⟨hw, (halfProjection_physical_interval_iff L hL3 w hw).mpr hc⟩
    · rintro ⟨hw, hc⟩
      exact ⟨hw, (halfProjection_physical_interval_iff L hL3 w hw).mp hc⟩

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
namespace StarProbabilitySpace
variable (φ : FreeProbability.StarProbabilitySpace A)

/-- The actual Cauchy parameter belongs to the standard physical domain. -/
theorem halfProjectionExteriorW_mem_physical_domain
    (hφ : IsTracial φ.toProbabilitySpace) (L : ℕ) (hL : 2 ≤ L)
    {B : Fin L → Subalgebra ℂ A} (hf : FreelyIndependent φ.toProbabilitySpace B)
    (p : Fin L → A) (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, IsStarProjection (p i))
    (hE : ∀ i, φ.expectation (p i) = (1 / 2 : ℂ)) (x : ℝ) (hx : halfProjectionRightEdge L < x) :
    halfProjectionPhysicalDomain L (φ.halfProjectionExteriorW L p hp x) := by
  apply (halfProjectionPhysicalDomain_iff L hL _).mpr
  exact ⟨φ.halfProjectionExteriorW_pos hφ L hL hf p hpB hp hE x hx,
    (φ.halfProjectionExteriorW_physical_interval hφ L hL hf p hpB hp hE x hx).2⟩

/-- The standard-domain root is unique, with its existence furnished by the
actual probability-law Cauchy transform on the full right exterior. -/
theorem existsUnique_halfProjection_standard_physical_root
    (hφ : IsTracial φ.toProbabilitySpace) (L : ℕ) (hL : 2 ≤ L)
    {B : Fin L → Subalgebra ℂ A} (hf : FreelyIndependent φ.toProbabilitySpace B)
    (p : Fin L → A) (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, IsStarProjection (p i))
    (hE : ∀ i, φ.expectation (p i) = (1 / 2 : ℂ)) (x : ℝ) (hx : halfProjectionRightEdge L < x) :
    ∃! w : ℝ, halfProjectionPhysicalDomain L w ∧ halfProjectionExteriorCurve L w = x := by
  refine ⟨φ.halfProjectionExteriorW L p hp x, ⟨?_, ?_⟩, ?_⟩
  · exact φ.halfProjectionExteriorW_mem_physical_domain hφ L hL hf p hpB hp hE x hx
  · exact φ.halfProjectionExteriorW_curve_equation hφ L hL hf p hpB hp hE x hx
  · intro w hw
    have hd := (halfProjectionPhysicalDomain_iff L hL w).mp hw.1
    exact φ.halfProjectionExteriorW_unique_physical hφ L hL hf p hpB hp hE x hx hd.1 hd.2 hw.2
end StarProbabilitySpace
end FreeProbability

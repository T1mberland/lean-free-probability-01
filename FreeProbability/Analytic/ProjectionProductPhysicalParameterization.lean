import FreeProbability.Analytic.ProjectionProductPhysicalDomain

/-! # Complete exterior parameterization by the actual physical branch -/

noncomputable section
namespace FreeProbability

/-- Every standard physical parameter maps into the genuine right exterior. -/
theorem halfProjectionExteriorCurve_gt_edge (L : ℕ) (hL : 2 ≤ L)
    {w : ℝ} (hw : halfProjectionPhysicalDomain L w) :
    halfProjectionRightEdge L < halfProjectionExteriorCurve L w := by
  have hd := (halfProjectionPhysicalDomain_iff L hL w).mp hw
  have hq : 0 < w / (1 + w) := div_pos hd.1 (by linarith)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, L = m + 2 := ⟨L - 2, (Nat.sub_add_cancel hL).symm⟩
  have hf : halfProjectionQParameter L (w / (1 + w)) < halfProjectionMomentThreshold L := by
    rw [← halfProjectionQParameter_at_critical L hL]
    have hc := halfProjectionCriticalQ_pos L hL
    simpa only [← hm] using (halfProjectionQParameter_strictMonoOn m)
      (by simpa only [← hm, Set.mem_Ioc] using And.intro hq hd.2.le)
      (by simpa only [← hm, Set.mem_Ioc] using And.intro hc (le_refl (halfProjectionCriticalQ L)))
      (by simpa only [← hm] using hd.2)
  have hepos : 0 < halfProjectionExteriorCurve L w :=
    div_pos (pow_pos (by linarith [hd.1]) L) (mul_pos hd.1 (pow_pos (by linarith [hd.1]) _))
  rw [halfProjectionQParameter_normalize L (by omega) w hd.1,
    halfProjectionMomentThreshold_eq_reciprocal] at hf
  exact (one_div_lt_one_div hepos (halfProjectionRightEdge_pos L hL)).mp hf

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
namespace StarProbabilitySpace
variable (φ : FreeProbability.StarProbabilitySpace A)

/-- All physical parameters are realized by the genuine law Cauchy branch,
so the exterior parameterization is exact in both directions. -/
theorem halfProjectionExteriorW_curve_inverse
    (hφ : IsTracial φ.toProbabilitySpace) (L : ℕ) (hL : 2 ≤ L)
    {B : Fin L → Subalgebra ℂ A} (hf : FreelyIndependent φ.toProbabilitySpace B)
    (p : Fin L → A) (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, IsStarProjection (p i))
    (hE : ∀ i, φ.expectation (p i) = (1 / 2 : ℂ))
    {w : ℝ} (hw : halfProjectionPhysicalDomain L w) :
    φ.halfProjectionExteriorW L p hp (halfProjectionExteriorCurve L w) = w := by
  have hd := (halfProjectionPhysicalDomain_iff L hL w).mp hw
  exact (φ.halfProjectionExteriorW_unique_physical hφ L hL hf p hpB hp hE
    (halfProjectionExteriorCurve L w) (halfProjectionExteriorCurve_gt_edge L hL hw)
    hd.1 hd.2 rfl).symm

/-- The rational exterior curve maps exactly onto the full exterior of the
actual product law, with the length-two boundary included. -/
theorem halfProjectionExteriorCurve_image_physical_domain
    (hφ : IsTracial φ.toProbabilitySpace) (L : ℕ) (hL : 2 ≤ L)
    {B : Fin L → Subalgebra ℂ A} (hf : FreelyIndependent φ.toProbabilitySpace B)
    (p : Fin L → A) (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, IsStarProjection (p i))
    (hE : ∀ i, φ.expectation (p i) = (1 / 2 : ℂ)) :
    halfProjectionExteriorCurve L '' {w | halfProjectionPhysicalDomain L w} =
      Set.Ioi (halfProjectionRightEdge L) := by
  apply Set.Subset.antisymm
  · rintro x ⟨w, hw, rfl⟩
    exact halfProjectionExteriorCurve_gt_edge L hL hw
  · intro x hx
    exact ⟨φ.halfProjectionExteriorW L p hp x,
      φ.halfProjectionExteriorW_mem_physical_domain hφ L hL hf p hpB hp hE x hx,
      φ.halfProjectionExteriorW_curve_equation hφ L hL hf p hpB hp hE x hx⟩
end StarProbabilitySpace
end FreeProbability

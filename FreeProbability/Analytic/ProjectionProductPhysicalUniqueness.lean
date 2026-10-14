import FreeProbability.Analytic.ProjectionProductPhysicalSelection

/-! # Uniqueness of the actual physical exterior branch -/

noncomputable section
namespace FreeProbability

/-- Normalization turns the exterior curve into the reciprocal moment parameter. -/
theorem halfProjectionQParameter_normalize (L : ℕ) (hL : 1 ≤ L)
    (w : ℝ) (hw : 0 < w) :
    halfProjectionQParameter L (w / (1 + w)) = 1 / halfProjectionExteriorCurve L w := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, L = n + 1 := ⟨L - 1, (Nat.sub_add_cancel hL).symm⟩
  have h1 : 1 + w ≠ 0 := by linarith
  have hh : w + (1 / 2 : ℝ) ≠ 0 := by linarith
  have hs : 1 + w / (1 + w) = (2 * (w + (1 / 2 : ℝ))) / (1 + w) := by
    field_simp
    ring
  unfold halfProjectionQParameter halfProjectionExteriorCurve
  rw [hs, div_pow, mul_pow]
  simp only [Nat.add_sub_cancel, one_div_div]
  rw [pow_succ (1 + w)]
  field_simp

/-- Positive exterior roots with a physical normalized parameter are unique. -/
theorem halfProjectionExteriorCurve_injective_physical (L : ℕ) (hL : 2 ≤ L)
    {v w : ℝ} (hv : 0 < v) (hw : 0 < w)
    (hvc : v / (1 + v) < halfProjectionCriticalQ L)
    (hwc : w / (1 + w) < halfProjectionCriticalQ L)
    (he : halfProjectionExteriorCurve L v = halfProjectionExteriorCurve L w) : v = w := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, L = m + 2 := ⟨L - 2, (Nat.sub_add_cancel hL).symm⟩
  have hvq : 0 < v / (1 + v) := div_pos hv (by linarith)
  have hwq : 0 < w / (1 + w) := div_pos hw (by linarith)
  have heq : halfProjectionQParameter L (v / (1 + v)) =
      halfProjectionQParameter L (w / (1 + w)) := by
    rw [halfProjectionQParameter_normalize L (by omega) v hv,
      halfProjectionQParameter_normalize L (by omega) w hw, he]
  have hq := (halfProjectionQParameter_strictMonoOn m).injOn
    (show v / (1 + v) ∈ Set.Ioc 0 (halfProjectionCriticalQ (m + 2)) by simpa [← hm] using And.intro hvq hvc.le)
    (show w / (1 + w) ∈ Set.Ioc 0 (halfProjectionCriticalQ (m + 2)) by simpa [← hm] using And.intro hwq hwc.le)
    (by simpa [← hm] using heq)
  have hv1 : 1 + v ≠ 0 := by linarith
  have hw1 : 1 + w ≠ 0 := by linarith
  have hc := (div_eq_div_iff hv1 hw1).mp hq
  nlinarith

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
namespace StarProbabilitySpace
variable (φ : FreeProbability.StarProbabilitySpace A)

/-- The actual law Cauchy parameter is the unique positive root on the physical
branch throughout the full right exterior, including length two. -/
theorem halfProjectionExteriorW_unique_physical
    (hφ : IsTracial φ.toProbabilitySpace) (L : ℕ) (hL : 2 ≤ L)
    {B : Fin L → Subalgebra ℂ A} (hf : FreelyIndependent φ.toProbabilitySpace B)
    (p : Fin L → A) (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, IsStarProjection (p i))
    (hE : ∀ i, φ.expectation (p i) = (1 / 2 : ℂ)) (x : ℝ) (hx : halfProjectionRightEdge L < x)
    {w : ℝ} (hw : 0 < w) (hwc : w / (1 + w) < halfProjectionCriticalQ L)
    (he : halfProjectionExteriorCurve L w = x) :
    w = φ.halfProjectionExteriorW L p hp x := by
  apply halfProjectionExteriorCurve_injective_physical L hL hw
    (φ.halfProjectionExteriorW_pos hφ L hL hf p hpB hp hE x hx) hwc
    (φ.halfProjectionExteriorW_physical_interval hφ L hL hf p hpB hp hE x hx).2
  exact he.trans (φ.halfProjectionExteriorW_curve_equation hφ L hL hf p hpB hp hE x hx).symm

/-- Existence and uniqueness refer to the genuine law Cauchy transform,
not an independently chosen algebraic root. -/
theorem existsUnique_halfProjection_physical_root
    (hφ : IsTracial φ.toProbabilitySpace) (L : ℕ) (hL : 2 ≤ L)
    {B : Fin L → Subalgebra ℂ A} (hf : FreelyIndependent φ.toProbabilitySpace B)
    (p : Fin L → A) (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, IsStarProjection (p i))
    (hE : ∀ i, φ.expectation (p i) = (1 / 2 : ℂ)) (x : ℝ) (hx : halfProjectionRightEdge L < x) :
    ∃! w : ℝ, 0 < w ∧ w / (1 + w) < halfProjectionCriticalQ L ∧
      halfProjectionExteriorCurve L w = x := by
  refine ⟨φ.halfProjectionExteriorW L p hp x, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact φ.halfProjectionExteriorW_pos hφ L hL hf p hpB hp hE x hx
  · exact (φ.halfProjectionExteriorW_physical_interval hφ L hL hf p hpB hp hE x hx).2
  · exact φ.halfProjectionExteriorW_curve_equation hφ L hL hf p hpB hp hE x hx
  · intro w hw
    exact φ.halfProjectionExteriorW_unique_physical hφ L hL hf p hpB hp hE x hx hw.1 hw.2.1 hw.2.2
end StarProbabilitySpace
end FreeProbability

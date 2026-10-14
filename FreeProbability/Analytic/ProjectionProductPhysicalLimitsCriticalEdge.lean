import FreeProbability.Analytic.ProjectionProductPhysicalParameterization

/-! # Critical coordinates and the actual probability-law edge -/

noncomputable section
open scoped Topology
namespace FreeProbability

/-- For length above two the finite critical exterior coordinate normalizes
to the critical moment coordinate. -/
theorem halfProjection_normalize_critical (L : ℕ) (hL : 3 ≤ L) :
    (1 / ((L : ℝ) - 2)) / (1 + 1 / ((L : ℝ) - 2)) = halfProjectionCriticalQ L := by
  have hLr : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have h2 : (L : ℝ) - 2 ≠ 0 := by linarith
  have h1 : (L : ℝ) - 1 ≠ 0 := by linarith
  unfold halfProjectionCriticalQ
  have hs : 1 + 1 / ((L : ℝ) - 2) = ((L : ℝ) - 1) / ((L : ℝ) - 2) := by
    field_simp
    ring
  rw [hs]
  field_simp [h2, h1]

/-- The finite critical exterior value is the genuine proposed edge,
not just a formal derivative zero. -/
theorem halfProjectionExteriorCurve_critical (L : ℕ) (hL : 3 ≤ L) :
    halfProjectionExteriorCurve L (1 / ((L : ℝ) - 2)) = halfProjectionRightEdge L := by
  have hLr : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hw : 0 < 1 / ((L : ℝ) - 2) := one_div_pos.mpr (by linarith)
  have he := halfProjectionQParameter_normalize L (by omega) _ hw
  rw [halfProjection_normalize_critical L hL,
    halfProjectionQParameter_at_critical L (by omega),
    halfProjectionMomentThreshold_eq_reciprocal] at he
  simp only [one_div] at he ⊢
  exact inv_injective he.symm

/-- The normalized critical point is an actual stationary point for all
lengths, including the boundary length two. -/
theorem hasDerivAt_halfProjectionQParameter_critical (L : ℕ) (hL : 2 ≤ L) :
    HasDerivAt (halfProjectionQParameter L) 0 (halfProjectionCriticalQ L) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, L = m + 2 := ⟨L - 2, (Nat.sub_add_cancel hL).symm⟩
  have h := hasDerivAt_halfProjectionQParameter m (halfProjectionCriticalQ (m + 2))
    (halfProjectionCriticalQ_pos _ (by omega)).le
  convert h using 1
  unfold halfProjectionCriticalQ
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  push_cast
  have he : (m : ℝ) + 2 - 1 = (m : ℝ) + 1 := by ring
  rw [he]
  simp [hm]

/-- The finite critical coordinate is a genuine stationary point of the
original exterior curve when the length is above two. -/
theorem hasDerivAt_halfProjectionExteriorCurve_critical (L : ℕ) (hL : 3 ≤ L) :
    HasDerivAt (halfProjectionExteriorCurve L) 0 (1 / ((L : ℝ) - 2)) := by
  let w : ℝ := 1 / ((L : ℝ) - 2)
  have hLr : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hw : 0 < w := one_div_pos.mpr (by linarith)
  have h1 : 1 + w ≠ 0 := by linarith
  have hq := (hasDerivAt_id w).div ((hasDerivAt_const w (1 : ℝ)).add (hasDerivAt_id w)) h1
  have hF := hasDerivAt_halfProjectionQParameter_critical L (by omega)
  rw [← halfProjection_normalize_critical L hL] at hF
  have hcomp := hF.comp w hq
  have hnon : halfProjectionQParameter L (w / (1 + w)) ≠ 0 := by
    rw [show w / (1 + w) = halfProjectionCriticalQ L from halfProjection_normalize_critical L hL,
      halfProjectionQParameter_at_critical L (by omega)]
    exact ne_of_gt (halfProjectionMomentThreshold_pos L (by omega))
  have hinv := hcomp.inv hnon
  simp only [zero_mul, neg_zero, zero_div] at hinv
  apply hinv.congr_of_eventuallyEq
  have hnear : ∀ᶠ v : ℝ in 𝓝 w, 0 < v :=
    (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) w).eventually_lt continuousAt_id hw
  filter_upwards [hnear] with v hv
  change halfProjectionExteriorCurve L v = (halfProjectionQParameter L (v / (1 + v)))⁻¹
  rw [halfProjectionQParameter_normalize L (by omega) v hv]
  simp only [one_div, inv_inv]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
namespace StarProbabilitySpace
variable (φ : FreeProbability.StarProbabilitySpace A)

/-- The finite critical exterior value is the greatest point of the ACTUAL
law support, independently of faithfulness of the ambient state. -/
theorem iteratedHalfProjection_law_support_critical_isGreatest
    (hφ : IsTracial φ.toProbabilitySpace) (L : ℕ) (hL : 3 ≤ L)
    {B : Fin L → Subalgebra ℂ A} (hf : FreelyIndependent φ.toProbabilitySpace B)
    (p : Fin L → A) (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, IsStarProjection (p i))
    (hE : ∀ i, φ.expectation (p i) = (1 / 2 : ℂ)) :
    IsGreatest ((iteratedPositiveProbabilityLaw φ L p (fun i => (hp i).nonneg) :
      MeasureTheory.Measure ℝ).support)
      (halfProjectionExteriorCurve L (1 / ((L : ℝ) - 2))) := by
  rw [halfProjectionExteriorCurve_critical L hL]
  exact φ.iteratedHalfProjection_law_support_isGreatest hφ L (by omega) hf p hpB hp hE
end StarProbabilitySpace
end FreeProbability

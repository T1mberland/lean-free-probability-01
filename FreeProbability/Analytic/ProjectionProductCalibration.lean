import FreeProbability.Analytic.ProjectionProductMomentSummability
import Mathlib.Topology.Order.LeftRight

/-! # Scalar calibration of genuine projection moment supersolutions -/

noncomputable section
open scoped Topology NNReal
namespace FreeProbability

/-- The intended right edge of the half-projection product law. -/
def halfProjectionRightEdge (L : ℕ) : ℝ :=
  (L : ℝ) ^ L / ((2 : ℝ) ^ L * ((L : ℝ) - 1) ^ (L - 1))

/-- The reciprocal critical moment parameter. -/
def halfProjectionMomentThreshold (L : ℕ) : ℝ :=
  (2 : ℝ) ^ L * ((L : ℝ) - 1) ^ (L - 1) / (L : ℝ) ^ L

/-- The normalized critical parameter includes the boundary at length two. -/
def halfProjectionCriticalQ (L : ℕ) : ℝ := 1 / ((L : ℝ) - 1)

/-- The real normalized inverse moment curve. -/
def halfProjectionQParameter (L : ℕ) (q : ℝ) : ℝ :=
  (2 : ℝ) ^ L * q / (1 + q) ^ L

theorem halfProjectionRightEdge_pos (L : ℕ) (hL : 2 ≤ L) : 0 < halfProjectionRightEdge L := by
  have hLR : (2 : ℝ) ≤ L := by exact_mod_cast hL
  exact div_pos (pow_pos (by linarith) _) (mul_pos (pow_pos (by norm_num) _) (pow_pos (by linarith) _))

theorem halfProjectionMomentThreshold_pos (L : ℕ) (hL : 2 ≤ L) : 0 < halfProjectionMomentThreshold L := by
  have hLR : (2 : ℝ) ≤ L := by exact_mod_cast hL
  exact div_pos (mul_pos (pow_pos (by norm_num) _) (pow_pos (by linarith) _)) (pow_pos (by linarith) _)

theorem halfProjectionMomentThreshold_eq_reciprocal (L : ℕ) :
    halfProjectionMomentThreshold L = 1 / halfProjectionRightEdge L := by
  simp [halfProjectionMomentThreshold, halfProjectionRightEdge, one_div, inv_div]

theorem halfProjectionCriticalQ_pos (L : ℕ) (hL : 2 ≤ L) : 0 < halfProjectionCriticalQ L := by
  have hLR : (2 : ℝ) ≤ L := by exact_mod_cast hL
  exact one_div_pos.mpr (by linarith)

theorem halfProjectionCriticalQ_le_one (L : ℕ) (hL : 2 ≤ L) : halfProjectionCriticalQ L ≤ 1 := by
  have hLR : (2 : ℝ) ≤ L := by exact_mod_cast hL
  exact (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) (by linarith : (1 : ℝ) ≤ (L : ℝ) - 1)).trans_eq (by simp)

/-- The actual normalized critical value is exactly the reciprocal proposed
edge, including length two. No spectral support conclusion is asserted here. -/
theorem halfProjectionQParameter_at_critical (L : ℕ) (hL : 2 ≤ L) :
    halfProjectionQParameter L (halfProjectionCriticalQ L) = halfProjectionMomentThreshold L := by
  have hLR : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hd : (L : ℝ) - 1 ≠ 0 := by linarith
  have hl : (L : ℝ) ≠ 0 := by linarith
  have hplus : 1 + halfProjectionCriticalQ L = (L : ℝ) / ((L : ℝ) - 1) := by
    unfold halfProjectionCriticalQ
    field_simp
    ring
  unfold halfProjectionQParameter
  rw [hplus]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, L = k + 1 := ⟨L - 1, (Nat.sub_add_cancel (by omega)).symm⟩
  rw [hk]
  simp only [halfProjectionCriticalQ, halfProjectionMomentThreshold, Nat.add_sub_cancel, div_pow]
  rw [pow_succ (((k + 1 : ℕ) : ℝ) - 1)]
  field_simp
  exact div_self (by simpa [hk] using hd)
/-- Every parameter strictly below the critical reciprocal edge has a
positive scalar supersolution strictly below one. This includes length two. -/
theorem exists_halfProjection_picard_supersolution (L : ℕ) (hL : 2 ≤ L)
    (t : ℝ) (ht : t < halfProjectionMomentThreshold L) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ (t / (2 : ℝ) ^ L) * (1 + r) ^ L ≤ r := by
  have hr0 := halfProjectionCriticalQ_pos L hL
  have hc : ContinuousAt (halfProjectionQParameter L) (halfProjectionCriticalQ L) := by
    have hn : ContinuousAt (fun q : ℝ => (2 : ℝ) ^ L * q) (halfProjectionCriticalQ L) :=
      continuousAt_const.mul continuousAt_id
    have hd : ContinuousAt (fun q : ℝ => (1 + q) ^ L) (halfProjectionCriticalQ L) :=
      (continuousAt_const.add continuousAt_id).pow L
    exact hn.div hd (pow_ne_zero L (by linarith))
  have hnear : ∀ᶠ r in 𝓝 (halfProjectionCriticalQ L), t < halfProjectionQParameter L r ∧ 0 < r :=
    ((continuousAt_const : ContinuousAt (fun _ : ℝ => t) (halfProjectionCriticalQ L)).eventually_lt hc
      (by rw [halfProjectionQParameter_at_critical L hL]; exact ht)).and
      ((continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) (halfProjectionCriticalQ L)).eventually_lt
        continuousAt_id hr0)
  obtain ⟨r, hrcrit, htr, hr⟩ := hnear.exists_lt
  refine ⟨r, hr, hrcrit.trans_le (halfProjectionCriticalQ_le_one L hL), ?_⟩
  have hden : 0 < (1 + r) ^ L := pow_pos (by linarith) L
  have htwo : 0 < (2 : ℝ) ^ L := pow_pos (by norm_num) L
  have hnum : t * (1 + r) ^ L < (2 : ℝ) ^ L * r :=
    (lt_div_iff₀ hden).mp htr
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ htwo).mpr (by simpa only [mul_comm] using hnum.le)

namespace StarProbabilitySpace
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (φ : FreeProbability.StarProbabilitySpace A)

/-- The ACTUAL law of every supplied free half-projection family has its
right support bounded by the intended sharp edge, including length two.
The matching lower bound and physical-branch theorem are separate. -/
theorem iteratedHalfProjection_law_support_sharp_upper
    (hφ : IsTracial φ.toProbabilitySpace) (L : ℕ) (hL : 2 ≤ L)
    {B : Fin L → Subalgebra ℂ A} (hf : FreelyIndependent φ.toProbabilitySpace B)
    (p : Fin L → A) (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, IsStarProjection (p i))
    (hE : ∀ i, φ.expectation (p i) = (1 / 2 : ℂ)) :
    (iteratedPositiveProbabilityLaw φ L p (fun i => (hp i).nonneg) : MeasureTheory.Measure ℝ).support ⊆
      Set.Iic (halfProjectionRightEdge L) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, L = n + 1 := ⟨L - 1, (Nat.sub_add_cancel (by omega)).symm⟩
  intro x hx
  change x ≤ halfProjectionRightEdge (n + 1)
  apply le_of_forall_gt_imp_ge_of_dense
  intro b hb
  have hedge := halfProjectionRightEdge_pos (n + 1) hL
  have hb0 : 0 < b := hedge.trans hb
  have ht : 1 / b < halfProjectionMomentThreshold (n + 1) := by
    rw [halfProjectionMomentThreshold_eq_reciprocal]
    exact one_div_lt_one_div_of_lt hedge hb
  obtain ⟨r, hr, hr1, hsuper⟩ := exists_halfProjection_picard_supersolution (n + 1) hL (1 / b) ht
  let t : ℝ≥0 := ⟨1 / b, (one_div_pos.mpr hb0).le⟩
  have hbound := φ.iteratedHalfProjection_law_support_of_picard_supersolution hφ n hf p hpB hp hE
    t (by exact_mod_cast (one_div_pos.mpr hb0)) r hr.le hr1 hsuper hx
  change x ≤ 1 / (1 / b) at hbound
  simpa using hbound
end StarProbabilitySpace
end FreeProbability

import FreeProbability.Analytic.ProjectionProductCalibration
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # The normalized projection curve has its exact global maximum -/

noncomputable section
open Set
namespace FreeProbability

/-- Direct differentiation of the normalized reciprocal curve. -/
theorem hasDerivAt_halfProjectionQParameter (m : ℕ) (q : ℝ) (hq : 0 ≤ q) :
    HasDerivAt (halfProjectionQParameter (m + 2))
      ((2 : ℝ) ^ (m + 2) * (1 - ((m : ℝ) + 1) * q) / (1 + q) ^ (m + 3)) q := by
  have hnum := (hasDerivAt_id q).const_mul ((2 : ℝ) ^ (m + 2))
  have hden := ((hasDerivAt_const q (1 : ℝ)).add (hasDerivAt_id q)).pow (m + 2)
  have hb : 1 + q ≠ 0 := by linarith
  have h := hnum.div hden (pow_ne_zero _ hb)
  convert h using 1
  · rfl
  · have hsub : m + 2 - 1 = m + 1 := by omega
    simp only [hsub, Nat.cast_add, Nat.cast_ofNat, Pi.pow_apply, Pi.add_apply, id_eq,
      mul_one, zero_add, pow_succ]
    field_simp [hb]
    ring

private theorem criticalQ_add_two (m : ℕ) : halfProjectionCriticalQ (m + 2) = 1 / ((m : ℝ) + 1) := by
  unfold halfProjectionCriticalQ
  congr 1
  push_cast
  ring

/-- The normalized curve increases before its critical point. -/
theorem halfProjectionQParameter_strictMonoOn (m : ℕ) :
    StrictMonoOn (halfProjectionQParameter (m + 2))
      (Ioc 0 (halfProjectionCriticalQ (m + 2))) := by
  have hc : 0 < halfProjectionCriticalQ (m + 2) := halfProjectionCriticalQ_pos _ (by omega)
  have hm : 0 < (m : ℝ) + 1 := by positivity
  apply strictMonoOn_of_deriv_pos (convex_Ioc _ _)
  · intro q hq
    exact (hasDerivAt_halfProjectionQParameter m q hq.1.le).continuousAt.continuousWithinAt
  · intro q hq
    rw [interior_Ioc] at hq
    rw [(hasDerivAt_halfProjectionQParameter m q hq.1.le).deriv]
    have hcrit : q < 1 / ((m : ℝ) + 1) := by
      simpa only [criticalQ_add_two] using hq.2
    have hprod : ((m : ℝ) + 1) * q < 1 := by
      simpa only [mul_comm] using (lt_div_iff₀ hm).mp hcrit
    exact div_pos (mul_pos (pow_pos (by norm_num) _) (by linarith)) (pow_pos (by linarith [hq.1]) _)

/-- The normalized curve decreases after its critical point, including
length two where the critical normalized parameter equals one. -/
theorem halfProjectionQParameter_strictAntiOn (m : ℕ) :
    StrictAntiOn (halfProjectionQParameter (m + 2))
      (Ici (halfProjectionCriticalQ (m + 2))) := by
  have hc : 0 < halfProjectionCriticalQ (m + 2) := halfProjectionCriticalQ_pos _ (by omega)
  have hm : 0 < (m : ℝ) + 1 := by positivity
  apply strictAntiOn_of_deriv_neg (convex_Ici _)
  · intro q hq
    exact (hasDerivAt_halfProjectionQParameter m q (hc.trans_le hq).le).continuousAt.continuousWithinAt
  · intro q hq
    rw [interior_Ici] at hq
    have hqp : 0 < q := hc.trans hq
    rw [(hasDerivAt_halfProjectionQParameter m q hqp.le).deriv]
    have hcrit : 1 / ((m : ℝ) + 1) < q := by
      simpa only [criticalQ_add_two, Set.mem_Ioi] using hq
    have hprod : 1 < ((m : ℝ) + 1) * q := by
      simpa only [mul_comm] using (div_lt_iff₀ hm).mp hcrit
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (pow_pos (by norm_num) _) (by linarith))
      (pow_pos (by linarith) _)

/-- The normalized inverse parameter never exceeds the reciprocal proposed
edge at any nonnegative parameter. This is the supercritical obstruction. -/
theorem halfProjectionQParameter_le_threshold (L : ℕ) (hL : 2 ≤ L) (q : ℝ) (hq : 0 ≤ q) :
    halfProjectionQParameter L q ≤ halfProjectionMomentThreshold L := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, L = m + 2 := ⟨L - 2, (Nat.sub_add_cancel hL).symm⟩
  by_cases hq0 : q = 0
  · subst q
    simp only [halfProjectionQParameter, mul_zero, zero_div]
    exact (halfProjectionMomentThreshold_pos _ (by omega)).le
  have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
  have hc : 0 < halfProjectionCriticalQ (m + 2) := halfProjectionCriticalQ_pos _ (by omega)
  rw [← halfProjectionQParameter_at_critical _ (by omega)]
  by_cases hle : q ≤ halfProjectionCriticalQ (m + 2)
  · exact (halfProjectionQParameter_strictMonoOn m).monotoneOn ⟨hqp, hle⟩ ⟨hc, le_rfl⟩ hle
  · have hge : halfProjectionCriticalQ (m + 2) ≤ q := (lt_of_not_ge hle).le
    exact (halfProjectionQParameter_strictAntiOn m).antitoneOn (Set.mem_Ici.mpr le_rfl)
      (Set.mem_Ici.mpr hge) hge
end FreeProbability

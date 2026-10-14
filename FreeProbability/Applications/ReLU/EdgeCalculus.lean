import FreeProbability.Applications.ReLU.EdgeParameter
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Algebra.Order.Field

/-! # Calculus of the rational free-projection edge parameter -/

namespace FreeProbability.ReLU

open Set

/-- Reciprocal of the depth `m+2` inverse-moment parameter. -/
noncomputable def reciprocalCurve (m : ℕ) (w : ℝ) : ℝ :=
  w * (1 + w) ^ (m + 1) / (w + 1 / 2) ^ (m + 2)

theorem reciprocalCurve_eq (m : ℕ) (w : ℝ) :
    reciprocalCurve m w = (projectionParameter (m + 2) w)⁻¹ := by
  simp [reciprocalCurve, projectionParameter, inv_div]

theorem reciprocalCurve_pos (m : ℕ) (w : ℝ) (hw : 0 < w) : 0 < reciprocalCurve m w := by
  unfold reciprocalCurve
  exact div_pos (mul_pos hw (pow_pos (by linarith) _)) (pow_pos (by linarith) _)

noncomputable def reciprocalDerivative (m : ℕ) (w : ℝ) : ℝ :=
  (1 + w) ^ m * (1 - (m : ℝ) * w) / (2 * (w + 1 / 2) ^ (m + 3))

/-- Direct differentiation gives the exact derivative, including the depth-two case. -/
theorem hasDerivAt_reciprocalCurve (m : ℕ) (w : ℝ) (hw : 0 < w) :
    HasDerivAt (reciprocalCurve m) (reciprocalDerivative m w) w := by
  have hnum := (hasDerivAt_id w).mul (((hasDerivAt_id w).const_add 1).pow (m + 1))
  have hden := ((hasDerivAt_id w).add_const (1 / 2 : ℝ)).pow (m + 2)
  have hbase : w + 1 / 2 ≠ 0 := by linarith
  have h := hnum.div hden (pow_ne_zero _ hbase)
  change HasDerivAt (fun t : ℝ => t * (1 + t) ^ (m + 1) / (t + 1 / 2) ^ (m + 2)) _ w
  convert h using 1
  · funext t
    rfl
  · unfold reciprocalDerivative
    have hm1 : m + 1 - 1 = m := by omega
    have hm2 : m + 2 - 1 = m + 1 := by omega
    simp only [hm1, hm2, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
      mul_one, one_mul, Pi.pow_apply, Pi.mul_apply, id_eq, pow_succ]
    field_simp [hbase]
    ring

theorem reciprocalDerivative_pos_before (m M : ℕ) (hM : 0 < M) (hm : m ≤ M)
    (w : ℝ) (hw : 0 < w) (hbound : w < 1 / (M : ℝ)) : 0 < reciprocalDerivative m w := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hmr : (m : ℝ) ≤ M := by exact_mod_cast hm
  have hMw : (M : ℝ) * w < 1 := by
    simpa [mul_comm] using (lt_div_iff₀ hMr).mp hbound
  have hmw : (m : ℝ) * w < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_right hmr hw.le) hMw
  unfold reciprocalDerivative
  exact div_pos (mul_pos (pow_pos (by linarith) _) (by linarith))
    (mul_pos (by norm_num) (pow_pos (by linarith) _))

/-- Every suffix reciprocal curve is increasing up to the full-depth critical point. -/
theorem reciprocalCurve_strictMonoOn (m M : ℕ) (hM : 0 < M) (hm : m ≤ M) :
    StrictMonoOn (reciprocalCurve m) (Ioc 0 (1 / (M : ℝ))) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioc _ _)
  · intro w hw
    exact (hasDerivAt_reciprocalCurve m w hw.1).continuousAt.continuousWithinAt
  · intro w hw
    rw [interior_Ioc] at hw
    rw [(hasDerivAt_reciprocalCurve m w hw.1).deriv]
    exact reciprocalDerivative_pos_before m M hM hm w hw.1 hw.2

theorem reciprocalDerivative_neg_after (m : ℕ) (hm : 0 < m) (w : ℝ)
    (hw : 1 / (m : ℝ) < w) : reciprocalDerivative m w < 0 := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hwp : 0 < w := lt_trans (div_pos (by norm_num) hmr) hw
  have hmw : 1 < (m : ℝ) * w := by simpa [mul_comm] using (div_lt_iff₀ hmr).mp hw
  unfold reciprocalDerivative
  apply div_neg_of_neg_of_pos
  · exact mul_neg_of_pos_of_neg (pow_pos (by linarith) _) (by linarith)
  · exact mul_pos (by norm_num) (pow_pos (by linarith) _)

theorem reciprocalCurve_strictAntiOn (m : ℕ) (hm : 0 < m) :
    StrictAntiOn (reciprocalCurve m) (Ici (1 / (m : ℝ))) := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hcrit : 0 < 1 / (m : ℝ) := div_pos (by norm_num) hmr
  apply strictAntiOn_of_deriv_neg (convex_Ici _)
  · intro w hw
    exact (hasDerivAt_reciprocalCurve m w (lt_of_lt_of_le hcrit hw)).continuousAt.continuousWithinAt
  · intro w hw
    rw [interior_Ici] at hw
    rw [(hasDerivAt_reciprocalCurve m w (lt_trans hcrit hw)).deriv]
    exact reciprocalDerivative_neg_after m hm w hw

theorem reciprocalCurve_le_at_critical (m : ℕ) (hm : 0 < m) (w : ℝ) (hw : 0 < w) :
    reciprocalCurve m w ≤ reciprocalCurve m (1 / (m : ℝ)) := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hc : 0 < 1 / (m : ℝ) := div_pos (by norm_num) hmr
  by_cases hle : w ≤ 1 / (m : ℝ)
  · exact (reciprocalCurve_strictMonoOn m m hm le_rfl).monotoneOn ⟨hw, hle⟩ ⟨hc, le_rfl⟩ hle
  · have hge : 1 / (m : ℝ) ≤ w := (lt_of_not_ge hle).le
    exact (reciprocalCurve_strictAntiOn m hm).antitoneOn
      (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hge) hge

theorem reciprocalCurve_eq_critical_iff (m : ℕ) (hm : 0 < m) (w : ℝ) (hw : 0 < w) :
    reciprocalCurve m w = reciprocalCurve m (1 / (m : ℝ)) ↔ w = 1 / (m : ℝ) := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hc : 0 < 1 / (m : ℝ) := div_pos (by norm_num) hmr
  constructor
  · intro he
    rcases lt_trichotomy w (1 / (m : ℝ)) with hlt | heq | hgt
    · exact False.elim ((ne_of_lt ((reciprocalCurve_strictMonoOn m m hm le_rfl)
        ⟨hw, hlt.le⟩ ⟨hc, le_rfl⟩ hlt)) he)
    · exact heq
    · exact False.elim ((ne_of_lt ((reciprocalCurve_strictAntiOn m hm)
        (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hgt.le) hgt)) he)
  · rintro rfl
    rfl

theorem projectionParameter_eq_inv (m : ℕ) (w : ℝ) :
    projectionParameter (m + 2) w = (reciprocalCurve m w)⁻¹ := by
  rw [reciprocalCurve_eq, inv_inv]

theorem edgeCandidate_eq_critical (m : ℕ) (hm : 0 < m) :
    edgeCandidate (m + 2) = projectionParameter (m + 2) (1 / (m : ℝ)) := by
  simpa [criticalParameter, Nat.cast_add] using
    (projectionParameter_edgeCandidate (m + 2) (by omega)).symm

/-- The rational parameter function has a global minimum at the asserted edge. -/
theorem projectionParameter_minimum (m : ℕ) (hm : 0 < m) (w : ℝ) (hw : 0 < w) :
    edgeCandidate (m + 2) ≤ projectionParameter (m + 2) w := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hc : 0 < 1 / (m : ℝ) := div_pos (by norm_num) hmr
  rw [edgeCandidate_eq_critical m hm, projectionParameter_eq_inv, projectionParameter_eq_inv]
  exact (inv_le_inv₀ (reciprocalCurve_pos m _ hc) (reciprocalCurve_pos m w hw)).mpr
    (reciprocalCurve_le_at_critical m hm w hw)

/-- Equality at the minimum occurs at exactly one positive parameter. -/
theorem projectionParameter_eq_edge_iff (m : ℕ) (hm : 0 < m) (w : ℝ) (hw : 0 < w) :
    projectionParameter (m + 2) w = edgeCandidate (m + 2) ↔ w = 1 / (m : ℝ) := by
  rw [edgeCandidate_eq_critical m hm, projectionParameter_eq_inv, projectionParameter_eq_inv,
    inv_inj]
  exact reciprocalCurve_eq_critical_iff m hm w hw

/-- The global rational-function minimum for every depth at least three. -/
theorem projectionParameter_isLeast (m : ℕ) (hm : 0 < m) :
    IsLeast (projectionParameter (m + 2) '' Ioi 0) (edgeCandidate (m + 2)) := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  refine ⟨⟨1 / (m : ℝ), div_pos (by norm_num) hmr, (edgeCandidate_eq_critical m hm).symm⟩, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  exact projectionParameter_minimum m hm w hw

theorem inverseParameter_one_mono (w v : ℝ) (hw : 0 < w) (hv : 0 < v) (hwv : w ≤ v) :
    (projectionParameter 1 w)⁻¹ ≤ (projectionParameter 1 v)⁻¹ := by
  simp only [projectionParameter, pow_one, Nat.sub_self, pow_zero, mul_one, inv_div]
  apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
  nlinarith

/-- Every reciprocal suffix parameter is bounded by its full-depth critical value. -/
theorem inverseParameter_le_critical (M k : ℕ) (hM : 0 < M) (hk : 1 ≤ k) (hkM : k ≤ M + 2)
    (w : ℝ) (hw : 0 < w) (hbound : w ≤ 1 / (M : ℝ)) :
    (projectionParameter k w)⁻¹ ≤ (projectionParameter k (1 / (M : ℝ)))⁻¹ := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hc : 0 < 1 / (M : ℝ) := div_pos (by norm_num) hMr
  by_cases hk1 : k = 1
  · subst k
    exact inverseParameter_one_mono w _ hw hc hbound
  · have hk2 : 2 ≤ k := by omega
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, (Nat.sub_add_cancel hk2).symm⟩
    rw [← reciprocalCurve_eq, ← reciprocalCurve_eq]
    exact (reciprocalCurve_strictMonoOn m M hM (by omega)).monotoneOn
      ⟨hw, hbound⟩ ⟨hc, le_rfl⟩ hbound

/-- Uniform scalar bound on the whole physical interval, not only at its endpoint. -/
theorem cavityLimitExpression_le_edge (M : ℕ) (hM : 0 < M) (w : ℝ)
    (hw : 0 < w) (hbound : w ≤ 1 / (M : ℝ)) :
    cavityLimitExpression (M + 2) w ≤ edgeSecularExpression (M + 2) := by
  have he : criticalParameter (M + 2) = 1 / (M : ℝ) := by simp [criticalParameter, Nat.cast_add]
  rw [← cavityLimitExpression_at_critical (M + 2) (by omega), he]
  unfold cavityLimitExpression
  apply add_le_add
  · apply Finset.sum_le_sum
    intro k hk
    have hklt : k < M + 2 - 1 := Finset.mem_range.mp hk
    simp only [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left
      (inverseParameter_le_critical M (k + 1) hM (by omega) (by omega) w hw hbound)
      (pow_nonneg (by norm_num) _)
  · simp only [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left
      (inverseParameter_le_critical M (M + 2) hM (by omega) le_rfl w hw hbound)
      (pow_nonneg (by norm_num) _)

theorem cavityLimitExpression_lt_one_on_physical (M : ℕ) (hM : 0 < M) (w : ℝ)
    (hw : 0 < w) (hbound : w ≤ 1 / (M : ℝ)) : cavityLimitExpression (M + 2) w < 1 :=
  lt_of_le_of_lt (cavityLimitExpression_le_edge M hM w hw hbound)
    (edgeSecularExpression_lt_one (M + 2) (by omega))

theorem cavityLimitExpression_strictMonoOn (M : ℕ) (hM : 0 < M) :
    StrictMonoOn (cavityLimitExpression (M + 2)) (Ioc 0 (1 / (M : ℝ))) := by
  intro w hw v hv hwv
  have hi (k : ℕ) (hk : 1 ≤ k) (hkM : k ≤ M + 2) :
      (projectionParameter k w)⁻¹ ≤ (projectionParameter k v)⁻¹ := by
    by_cases hk1 : k = 1
    · subst k
      exact inverseParameter_one_mono w v hw.1 hv.1 hwv.le
    · have hk2 : 2 ≤ k := by omega
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, (Nat.sub_add_cancel hk2).symm⟩
      rw [← reciprocalCurve_eq, ← reciprocalCurve_eq]
      exact (reciprocalCurve_strictMonoOn m M hM (by omega)).monotoneOn hw hv hwv.le
  have hs : (∑ k ∈ Finset.range (M + 2 - 1),
      (1 / 2 : ℝ) ^ (k + 1) / projectionParameter (k + 1) w) ≤
      ∑ k ∈ Finset.range (M + 2 - 1),
        (1 / 2 : ℝ) ^ (k + 1) / projectionParameter (k + 1) v := by
    apply Finset.sum_le_sum
    intro k hk
    simp only [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (hi (k + 1) (by omega) (by
      have := Finset.mem_range.mp hk
      omega)) (pow_nonneg (by norm_num) _)
  have ht : (1 / 2 : ℝ) ^ (M + 2 - 1) / projectionParameter (M + 2) w <
      (1 / 2 : ℝ) ^ (M + 2 - 1) / projectionParameter (M + 2) v := by
    simp only [div_eq_mul_inv, ← reciprocalCurve_eq]
    exact mul_lt_mul_of_pos_left
      (reciprocalCurve_strictMonoOn M M hM le_rfl hw hv hwv) (pow_pos (by norm_num) _)
  exact add_lt_add_of_le_of_lt hs ht

theorem cavityLimitExpression_two_lt_one (w : ℝ) (hw : 0 < w) :
    cavityLimitExpression 2 w < 1 := by
  have h0 : w ≠ 0 := hw.ne'
  have h1 : 1 + w ≠ 0 := by linarith
  have hhalf : w + 1 / 2 ≠ 0 := by linarith
  have he : cavityLimitExpression 2 w = 1 - (w + 1) / (4 * (w + 1 / 2) ^ 2) := by
    norm_num [cavityLimitExpression, projectionParameter, Finset.sum_range_succ]
    field_simp [h0, h1, hhalf]
    ring
  rw [he]
  have hp : 0 < (w + 1) / (4 * (w + 1 / 2) ^ 2) :=
    div_pos (by linarith) (mul_pos (by norm_num) (sq_pos_of_ne_zero hhalf))
  linarith

theorem projectionParameter_two_eq (w : ℝ) (hw : 0 < w) :
    projectionParameter 2 w = 1 + 1 / (4 * w * (1 + w)) := by
  have h0 : w ≠ 0 := hw.ne'
  have h1 : 1 + w ≠ 0 := by linarith
  norm_num [projectionParameter]
  field_simp [h0, h1]
  ring

theorem projectionParameter_two_gt_one (w : ℝ) (hw : 0 < w) : 1 < projectionParameter 2 w := by
  rw [projectionParameter_two_eq w hw]
  have hp : 0 < 1 / (4 * w * (1 + w)) :=
    div_pos (by norm_num) (mul_pos (mul_pos (by norm_num) hw) (by linarith))
  linarith

theorem projectionParameter_two_approaches_one (ε : ℝ) (hε : 0 < ε) :
    ∃ w : ℝ, 0 < w ∧ projectionParameter 2 w < 1 + ε := by
  refine ⟨1 / ε, div_pos (by norm_num) hε, ?_⟩
  rw [projectionParameter_two_eq _ (div_pos (by norm_num) hε)]
  have h0 : ε ≠ 0 := hε.ne'
  have h1 : 1 + ε ≠ 0 := by linarith
  have he : 1 / (4 * (1 / ε) * (1 + 1 / ε)) = ε ^ 2 / (4 * (1 + ε)) := by
    field_simp [h0, h1]
    ring
  rw [he]
  have hd : 0 < 4 * (1 + ε) := mul_pos (by norm_num) (by linarith)
  have hf : ε ^ 2 / (4 * (1 + ε)) < ε := (div_lt_iff₀ hd).mpr (by nlinarith [sq_nonneg ε])
  linarith

/-- The depth-two rational parameter has infimum one, with no finite minimizer. -/
theorem projectionParameter_two_isGLB : IsGLB (projectionParameter 2 '' Ioi 0) 1 := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact (projectionParameter_two_gt_one w hw).le
  · intro b hb
    by_contra hle
    have hb1 : 1 < b := lt_of_not_ge hle
    obtain ⟨w, hw, hval⟩ := projectionParameter_two_approaches_one (b - 1) (by linarith)
    have hbound : b ≤ projectionParameter 2 w := hb ⟨w, hw, rfl⟩
    linarith

theorem projectionParameter_two_tendsto :
    Filter.Tendsto (projectionParameter 2) Filter.atTop (nhds 1) := by
  have hden : Filter.Tendsto (fun w : ℝ => 4 * w * (1 + w)) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    filter_upwards [Filter.eventually_ge_atTop (max b 1)] with w hw
    have hb : b ≤ w := le_trans (le_max_left _ _) hw
    have h1 : 1 ≤ w := le_trans (le_max_right _ _) hw
    nlinarith
  have hi := tendsto_inv_atTop_zero.comp hden
  have ht : Filter.Tendsto (fun w : ℝ => 1 + (4 * w * (1 + w))⁻¹)
      Filter.atTop (nhds 1) := by simpa using tendsto_const_nhds.add hi
  apply ht.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with w hw
  simpa only [one_div] using (projectionParameter_two_eq w hw).symm

end FreeProbability.ReLU

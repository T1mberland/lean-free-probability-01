import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import FreeProbability.Applications.ReLU.Subcriticality

/-!
# Scalar inverse-moment parameterization for projection products

The rational functions are defined explicitly. Evaluation at the
critical parameter is proved here; the rational minimum and physical-interval
calculus are proved in `EdgeCalculus`. The free-law S-transform identification
remains a separate obligation.
-/

namespace FreeProbability.ReLU

noncomputable def projectionParameter (k : ℕ) (w : ℝ) : ℝ :=
  (w + 1 / 2) ^ k / (w * (1 + w) ^ (k - 1))

noncomputable def criticalParameter (L : ℕ) : ℝ := 1 / ((L : ℝ) - 2)

/-- The explicit candidate edge value, prior to identifying a spectral law. -/
noncomputable def edgeCandidate (L : ℕ) : ℝ :=
  (L : ℝ) ^ L / (2 ^ L * ((L : ℝ) - 1) ^ (L - 1))

theorem projectionParameter_at_critical (L k : ℕ) (hL : 3 ≤ L) (hk : 1 ≤ k) :
    projectionParameter k (criticalParameter L) =
      (L : ℝ) ^ k / (2 ^ k * ((L : ℝ) - 1) ^ (k - 1)) := by
  have hLR : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hd : (L : ℝ) - 2 ≠ 0 := by linarith
  have he : (L : ℝ) - 1 ≠ 0 := by linarith
  have hplus : criticalParameter L + 1 / 2 = (L : ℝ) / (2 * ((L : ℝ) - 2)) := by
    unfold criticalParameter
    field_simp
    ring
  have hsucc : 1 + criticalParameter L = ((L : ℝ) - 1) / ((L : ℝ) - 2) := by
    unfold criticalParameter
    field_simp
    ring
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 1 := ⟨k - 1, (Nat.sub_add_cancel hk).symm⟩
  simp only [projectionParameter, Nat.add_sub_cancel]
  rw [hplus, hsucc]
  simp only [criticalParameter, div_pow, mul_pow, pow_succ]
  field_simp [hd, he]

theorem projectionParameter_edgeCandidate (L : ℕ) (hL : 3 ≤ L) :
    projectionParameter L (criticalParameter L) = edgeCandidate L :=
  projectionParameter_at_critical L L hL (by omega)

theorem edgeCandidate_pos (L : ℕ) (hL : 3 ≤ L) : 0 < edgeCandidate L := by
  have hLR : (3 : ℝ) ≤ L := by exact_mod_cast hL
  unfold edgeCandidate
  apply div_pos
  · exact pow_pos (by linarith) _
  · exact mul_pos (pow_pos (by norm_num) _) (pow_pos (by linarith) _)

@[simp] theorem edgeCandidate_two : edgeCandidate 2 = 1 := by norm_num [edgeCandidate]
@[simp] theorem edgeCandidate_three : edgeCandidate 3 = (27 / 32 : ℝ) := by norm_num [edgeCandidate]
@[simp] theorem edgeCandidate_four : edgeCandidate 4 = (16 / 27 : ℝ) := by norm_num [edgeCandidate]

theorem weighted_inverse_parameter_at_critical (L k : ℕ) (hL : 3 ≤ L) (hk : 1 ≤ k) :
    (1 / 2 : ℝ) ^ k / projectionParameter k (criticalParameter L) =
      (1 / (L : ℝ)) * (1 - 1 / (L : ℝ)) ^ (k - 1) := by
  have hLR : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have h0 : (L : ℝ) ≠ 0 := by linarith
  have h1 : (L : ℝ) - 1 ≠ 0 := by linarith
  have hq : 1 - 1 / (L : ℝ) = ((L : ℝ) - 1) / (L : ℝ) := by
    field_simp [h0]
  rw [projectionParameter_at_critical L k hL hk, hq]
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 1 := ⟨k - 1, (Nat.sub_add_cancel hk).symm⟩
  simp only [Nat.add_sub_cancel, div_pow, pow_succ]
  field_simp [h0, h1]
  simp

/-- An explicit finite sum of reciprocal projection parameters.
Its interpretation as a spectral or probabilistic limit requires further results. -/
noncomputable def cavityLimitExpression (L : ℕ) (w : ℝ) : ℝ :=
  (∑ k ∈ Finset.range (L - 1),
    (1 / 2 : ℝ) ^ (k + 1) / projectionParameter (k + 1) w) +
      (1 / 2 : ℝ) ^ (L - 1) / projectionParameter L w

theorem cavityLimitExpression_at_critical (L : ℕ) (hL : 3 ≤ L) :
    cavityLimitExpression L (criticalParameter L) = edgeSecularExpression L := by
  have hsum : (∑ k ∈ Finset.range (L - 1),
      (1 / 2 : ℝ) ^ (k + 1) / projectionParameter (k + 1) (criticalParameter L)) =
        (1 / (L : ℝ)) * (∑ k ∈ Finset.range (L - 1), (1 - 1 / (L : ℝ)) ^ k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simpa using weighted_inverse_parameter_at_critical L (k + 1) hL (by omega)
  have hpow : (1 / 2 : ℝ) ^ (L - 1) = 2 * (1 / 2 : ℝ) ^ L := by
    have hn : L - 1 + 1 = L := Nat.sub_add_cancel (by omega)
    calc
      _ = 2 * ((1 / 2 : ℝ) ^ (L - 1) * (1 / 2)) := by ring
      _ = 2 * (1 / 2 : ℝ) ^ L := by rw [← pow_succ, hn]
  unfold cavityLimitExpression edgeSecularExpression
  rw [hsum, hpow, mul_div_assoc,
    weighted_inverse_parameter_at_critical L L hL (by omega)]
  ring

/-- The actual rational cavity sum at the critical parameter is strictly below one. -/
theorem cavityLimitExpression_at_critical_lt_one (L : ℕ) (hL : 3 ≤ L) :
    cavityLimitExpression L (criticalParameter L) < 1 := by
  rw [cavityLimitExpression_at_critical L hL]
  exact edgeSecularExpression_lt_one L hL

end FreeProbability.ReLU

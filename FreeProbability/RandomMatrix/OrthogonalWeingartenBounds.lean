import FreeProbability.RandomMatrix.OrthogonalWeingartenAsymptotics

/-! # Uniform eventual error bounds for actual Weingarten entries -/

noncomputable section
open scoped Classical Topology
namespace FreeProbability.Orthogonal
open Filter Matrix

private theorem reciprocal_power_identity (x : ℝ) (hx : x ≠ 0) (c r : ℕ) (hcr : c ≤ r) :
    (x ^ r)⁻¹ * x ^ c = (x⁻¹) ^ (r - c) := by
  conv_lhs => rw [show r = c + (r - c) by omega, pow_add]
  simp only [_root_.mul_inv_rev, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hx), mul_one, inv_pow]

/-- Every entry of the true normalized Gram differs from the identity by at
most the reciprocal dimension, in every positive dimension. -/
theorem normalizedPairingGram_entry_error_le (r N : ℕ) (hN : 1 ≤ N)
    (p q : OrdinaryPairing r) :
    |normalizedPairingGram r N p q - (1 : Matrix (OrdinaryPairing r) (OrdinaryPairing r) ℝ) p q|
      ≤ (N : ℝ)⁻¹ := by
  have hx : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hx1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have he : normalizedPairingGram r N p q = ((N : ℝ)⁻¹) ^ (r - pairingLoopCount p q) := by
    rw [normalizedPairingGram_apply]
    exact reciprocal_power_identity _ hx _ _ (pairingLoopCount_le p q)
  rw [he, Matrix.one_apply]
  by_cases hpq : p = q
  · subst q
    simp only [(pairingLoopCount_eq_iff p p).mpr rfl, Nat.sub_self, pow_zero, ite_true,
      sub_self, abs_zero]
    positivity
  · simp only [hpq, ite_false, sub_zero, abs_of_nonneg (by positivity :
      0 ≤ ((N : ℝ)⁻¹) ^ (r - pairingLoopCount p q))]
    apply pow_le_of_le_one (by positivity) ((inv_le_one₀ (by positivity)).mpr hx1)
    have := pairingLoopCount_lt_of_ne p q hpq
    omega

/-- Genuine leading limits bound all rescaled inverse entries simultaneously. -/
theorem eventually_rescaledWeingartenWeight_abs_le_two (r : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ p q : OrdinaryPairing r,
      |(N : ℝ) ^ r * (ordinaryPairingGram (Fin N) r)⁻¹ p q| ≤ 2 := by
  apply Filter.eventually_all.mpr
  intro p
  apply Filter.eventually_all.mpr
  intro q
  have h := (tendsto_rescaledWeingartenWeight r p q).abs
  have hb : |if p = q then (1 : ℝ) else 0| < 2 := by split_ifs <;> norm_num
  filter_upwards [h.eventually_lt_const hb] with N hN
  exact hN.le

/-- The actual rescaled Weingarten matrix is a left inverse of the
normalized Gram in stable positive dimension. -/
theorem rescaledWeingarten_mul_normalizedPairingGram (r N : ℕ)
    (hr : r ≤ N) (hN : N ≠ 0) :
    ((N : ℝ) ^ r • (ordinaryPairingGram (Fin N) r)⁻¹) * normalizedPairingGram r N = 1 := by
  have hx : (N : ℝ) ^ r ≠ 0 := pow_ne_zero _ (by exact_mod_cast hN)
  rw [normalizedPairingGram, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    mul_inv_cancel₀ hx, one_smul]
  exact (ordinaryPairingGram_inverse r (by simpa only [Fintype.card_fin] using hr)).2

/-- Uniform reciprocal-dimension error for every TRUE dimension-rescaled
Weingarten entry. No asymptotic freeness assertion is made here. -/
theorem eventually_rescaledWeingartenWeight_error_le (r : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ p q : OrdinaryPairing r,
      |(N : ℝ) ^ r * (ordinaryPairingGram (Fin N) r)⁻¹ p q -
        (if p = q then (1 : ℝ) else 0)|
      ≤ 2 * (Fintype.card (OrdinaryPairing r) : ℝ) / (N : ℝ) := by
  filter_upwards [eventually_ge_atTop (max r 1),
    eventually_rescaledWeingartenWeight_abs_le_two r] with N hN hb
  intro p q
  let A := normalizedPairingGram r N
  let R : Matrix (OrdinaryPairing r) (OrdinaryPairing r) ℝ :=
    (N : ℝ) ^ r • (ordinaryPairingGram (Fin N) r)⁻¹
  have hRA : R * A = 1 := rescaledWeingarten_mul_normalizedPairingGram r N
    (le_max_left r 1 |>.trans hN) (by omega)
  have hid : R - 1 = R * (1 - A) := by rw [mul_sub, mul_one, hRA]
  change |(R - 1) p q| ≤ _
  rw [hid, Matrix.mul_apply]
  calc
    |∑ t, R p t * (1 - A) t q| ≤ ∑ t, |R p t * (1 - A) t q| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t : OrdinaryPairing r, 2 * (N : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro t _
      rw [abs_mul]
      apply mul_le_mul (hb p t)
      · change |(1 : Matrix (OrdinaryPairing r) (OrdinaryPairing r) ℝ) t q - A t q| ≤ _
        rw [abs_sub_comm]
        exact normalizedPairingGram_entry_error_le r N (le_max_right r 1 |>.trans hN) t q
      · positivity
      · norm_num
    _ = 2 * (Fintype.card (OrdinaryPairing r) : ℝ) / (N : ℝ) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, div_eq_mul_inv]
      ring

end FreeProbability.Orthogonal

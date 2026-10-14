import FreeProbability.RandomMatrix.OrthogonalWeingartenBounds
import FreeProbability.RandomMatrix.OrthogonalPairingDistance

/-! # Genuine distance-sensitive inverse bounds by finite expansion -/

noncomputable section
open scoped Classical Topology
namespace FreeProbability.Orthogonal
open Filter Matrix

private theorem scalar_power_identity (x : ℝ) (hx : x ≠ 0) (c r : ℕ) (hcr : c ≤ r) :
    (x ^ r)⁻¹ * x ^ c = (x⁻¹) ^ (r - c) := by
  conv_lhs => rw [show r = c + (r - c) by omega, pow_add]
  simp only [_root_.mul_inv_rev, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hx), mul_one, inv_pow]

/-- The actual normalized Gram entries are exactly powers of the reciprocal
dimension indexed by the genuine ordinary pairing distance. -/
theorem normalizedPairingGram_eq_distance_power (r N : ℕ) (hN : N ≠ 0)
    (p q : OrdinaryPairing r) :
    normalizedPairingGram r N p q = ((N : ℝ)⁻¹) ^ pairingDistance p q := by
  rw [normalizedPairingGram_apply]
  exact scalar_power_identity _ (by exact_mod_cast hN) _ _ (pairingLoopCount_le p q)

/-- There is always at least one intrinsic ordinary pairing, including degree zero. -/
theorem ordinaryPairing_card_pos (r : ℕ) : 0 < Fintype.card (OrdinaryPairing r) := by
  let e : PairingSites r := Fintype.equivOfCardEq (by simp [Nat.mul_comm])
  exact Fintype.card_pos_iff.mpr ⟨Quotient.mk _ e⟩

/-- Zeroth tensor degree is exactly scalar integration, even in dimension zero. -/
theorem rescaledWeingartenWeight_zero (N : ℕ) (p q : OrdinaryPairing 0) :
    (N : ℝ) ^ 0 * (ordinaryPairingGram (Fin N) 0)⁻¹ p q = 1 := by
  have hG : ordinaryPairingGram (Fin N) 0 = 1 := by
    ext a b
    have hab : a = b := Subsingleton.elim _ _
    have hc : pairingLoopCount a b = 0 := Nat.eq_zero_of_le_zero (pairingLoopCount_le a b)
    change (Fintype.card (Fin N) : ℝ) ^ pairingLoopCount a b = _
    rw [hc, pow_zero, Matrix.one_apply]
    simp only [hab, ite_true]
  rw [hG, inv_one, pow_zero, one_mul, Matrix.one_apply]
  simp only [Subsingleton.elim p q, ite_true]

private theorem error_entry_weighted (r N : ℕ) (hN : 1 ≤ N) (p q : OrdinaryPairing r) :
    |(1 - normalizedPairingGram r N) p q| ≤ ((N : ℝ)⁻¹) ^ pairingDistance p q := by
  change |(1 : Matrix (OrdinaryPairing r) (OrdinaryPairing r) ℝ) p q - normalizedPairingGram r N p q| ≤ _
  rw [normalizedPairingGram_eq_distance_power r N (by omega), Matrix.one_apply]
  by_cases h : p = q
  · subst q
    simp only [(pairingDistance_eq_zero_iff p p).mpr rfl, pow_zero, ite_true, sub_self, abs_zero]
    norm_num
  · simp only [h, ite_false, zero_sub, abs_neg, abs_of_nonneg (by positivity :
      0 ≤ ((N : ℝ)⁻¹) ^ pairingDistance p q), le_refl]

private theorem power_entry_weighted (r N : ℕ) (hN : 1 ≤ N) (k : ℕ)
    (p q : OrdinaryPairing r) :
    |((1 - normalizedPairingGram r N) ^ k) p q| ≤
      (Fintype.card (OrdinaryPairing r) : ℝ) ^ k * ((N : ℝ)⁻¹) ^ pairingDistance p q := by
  have hx0 : 0 ≤ (N : ℝ)⁻¹ := by positivity
  have hx1 : (N : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr (by exact_mod_cast hN)
  induction k generalizing p q with
  | zero =>
    simp only [pow_zero, Matrix.one_apply, one_mul]
    split_ifs with h
    · subst q
      simp only [(pairingDistance_eq_zero_iff p p).mpr rfl, pow_zero, abs_one, le_refl]
    · simp only [abs_zero]; positivity
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      ∑ t, |((1 - normalizedPairingGram r N) ^ k) p t * (1 - normalizedPairingGram r N) t q| ≤
          ∑ _t : OrdinaryPairing r,
            (Fintype.card (OrdinaryPairing r) : ℝ) ^ k * ((N : ℝ)⁻¹) ^ pairingDistance p q := by
        apply Finset.sum_le_sum
        intro t _
        rw [abs_mul]
        calc
          _ ≤ ((Fintype.card (OrdinaryPairing r) : ℝ) ^ k * ((N : ℝ)⁻¹) ^ pairingDistance p t) *
              ((N : ℝ)⁻¹) ^ pairingDistance t q :=
            mul_le_mul (ih p t) (error_entry_weighted r N hN t q) (abs_nonneg _) (by positivity)
          _ = (Fintype.card (OrdinaryPairing r) : ℝ) ^ k *
              ((N : ℝ)⁻¹) ^ (pairingDistance p t + pairingDistance t q) := by rw [pow_add]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (pow_le_pow_of_le_one hx0 hx1 (pairingDistance_triangle p t q)) (by positivity)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, pow_succ]; ring

private theorem power_entry_crude (r N : ℕ) (hN : 1 ≤ N) (k : ℕ)
    (p q : OrdinaryPairing r) :
    |((1 - normalizedPairingGram r N) ^ k) p q| ≤
      (Fintype.card (OrdinaryPairing r) : ℝ) ^ k * ((N : ℝ)⁻¹) ^ k := by
  induction k generalizing p q with
  | zero => simp only [pow_zero, Matrix.one_apply, mul_one]; split_ifs <;> norm_num
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      ∑ t, |((1 - normalizedPairingGram r N) ^ k) p t * (1 - normalizedPairingGram r N) t q| ≤
          ∑ _t : OrdinaryPairing r,
            ((Fintype.card (OrdinaryPairing r) : ℝ) ^ k * ((N : ℝ)⁻¹) ^ k) * (N : ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro t _
        rw [abs_mul]
        apply mul_le_mul (ih p t)
        · change |(1 : Matrix (OrdinaryPairing r) (OrdinaryPairing r) ℝ) t q - normalizedPairingGram r N t q| ≤ _
          rw [abs_sub_comm]
          exact normalizedPairingGram_entry_error_le r N hN t q
        · positivity
        · positivity
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, pow_succ]; ring

private theorem finite_inverse_expansion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R A : Matrix ι ι ℝ) (hRA : R * A = 1) (k : ℕ) :
    R = (∑ j ∈ Finset.range k, (1 - A) ^ j) + R * (1 - A) ^ k := by
  have hRE : R * (1 - A) = R - 1 := by rw [mul_sub, mul_one, hRA]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ', ← mul_assoc, hRE, sub_mul, one_mul]
    calc
      R = (∑ j ∈ Finset.range k, (1 - A) ^ j) + R * (1 - A) ^ k := ih
      _ = _ := by abel

/-- For fixed half-degree, every true rescaled Weingarten entry has the
sharp ordinary-distance decay, with one explicit constant and one threshold
for all pairings. The finite expansion includes the scalar degree-zero case. -/
theorem eventually_rescaledWeingartenWeight_distance_bound (r : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ p q : OrdinaryPairing r,
      |(N : ℝ) ^ r * (ordinaryPairingGram (Fin N) r)⁻¹ p q| ≤
        ((r : ℝ) * (Fintype.card (OrdinaryPairing r) : ℝ) ^ r +
          2 * (Fintype.card (OrdinaryPairing r) : ℝ) ^ (r + 1)) *
          ((N : ℝ)⁻¹) ^ pairingDistance p q := by
  filter_upwards [eventually_ge_atTop (max r 1),
    eventually_rescaledWeingartenWeight_abs_le_two r] with N hN hb
  intro p q
  have hN1 : 1 ≤ N := le_max_right r 1 |>.trans hN
  let M : ℝ := Fintype.card (OrdinaryPairing r)
  have hM : 1 ≤ M := by dsimp [M]; exact_mod_cast ordinaryPairing_card_pos r
  let E : Matrix (OrdinaryPairing r) (OrdinaryPairing r) ℝ := 1 - normalizedPairingGram r N
  let R : Matrix (OrdinaryPairing r) (OrdinaryPairing r) ℝ :=
    (N : ℝ) ^ r • (ordinaryPairingGram (Fin N) r)⁻¹
  have hRA : R * normalizedPairingGram r N = 1 :=
    rescaledWeingarten_mul_normalizedPairingGram r N (le_max_left r 1 |>.trans hN) (by omega)
  have he := congrArg (fun B : Matrix (OrdinaryPairing r) (OrdinaryPairing r) ℝ => B p q)
    (finite_inverse_expansion R (normalizedPairingGram r N) hRA r)
  have hsum : |(∑ k ∈ Finset.range r, E ^ k) p q| ≤
      (r : ℝ) * M ^ r * ((N : ℝ)⁻¹) ^ pairingDistance p q := by
    rw [Matrix.sum_apply]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      ∑ k ∈ Finset.range r, |(E ^ k) p q| ≤
          ∑ _k ∈ Finset.range r, M ^ r * ((N : ℝ)⁻¹) ^ pairingDistance p q := by
        apply Finset.sum_le_sum
        intro k hk
        exact (power_entry_weighted r N hN1 k p q).trans
          (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hM (Finset.mem_range.mp hk).le) (by positivity))
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  have htail : |(R * E ^ r) p q| ≤ 2 * M ^ (r + 1) * ((N : ℝ)⁻¹) ^ pairingDistance p q := by
    rw [Matrix.mul_apply]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      ∑ t, |R p t * (E ^ r) t q| ≤ ∑ _t : OrdinaryPairing r, 2 * (M ^ r * ((N : ℝ)⁻¹) ^ r) := by
        apply Finset.sum_le_sum
        intro t _
        rw [abs_mul]
        exact mul_le_mul (hb p t) (power_entry_crude r N hN1 r t q) (abs_nonneg _) (by norm_num)
      _ = 2 * M ^ (r + 1) * ((N : ℝ)⁻¹) ^ r := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, pow_succ]; dsimp [M]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one (by positivity)
          ((inv_le_one₀ (by positivity)).mpr (by exact_mod_cast hN1)) (Nat.sub_le r _)) (by positivity)
  change |R p q| ≤ _
  rw [he]
  exact (abs_add_le _ _).trans (by nlinarith [hsum, htail])

end FreeProbability.Orthogonal

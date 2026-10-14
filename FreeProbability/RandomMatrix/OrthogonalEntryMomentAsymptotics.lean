import FreeProbability.RandomMatrix.OrthogonalWeingartenBounds

/-! # Uniform leading pairing approximation for genuine Haar entry moments -/

noncomputable section
open scoped Classical Topology
namespace FreeProbability.Orthogonal
open Filter

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] in
/-- The ordinary paired delta is always between zero and one. -/
theorem ordinaryPairingDelta_abs_le_one {r : ℕ} (p : OrdinaryPairing r)
    (i : Fin (2 * r) → n) : |ordinaryPairingDelta p i| ≤ 1 := by
  unfold ordinaryPairingDelta
  rw [abs_of_nonneg (Finset.prod_nonneg (fun a _ => by split_ifs <;> norm_num))]
  exact Finset.prod_le_one₀ (fun a _ => by split_ifs <;> norm_num)
    (fun a _ => by split_ifs <;> norm_num)

/-- An exact error expansion for the actual rescaled Haar integral. -/
theorem rescaled_entryMoment_sub_pairing_sum {r N : ℕ} (hr : r ≤ N)
    (i j : Fin (2 * r) → Fin N) :
    (N : ℝ) ^ r * entryMoment i j -
      ∑ p : OrdinaryPairing r, ordinaryPairingDelta p i * ordinaryPairingDelta p j =
    ∑ p : OrdinaryPairing r, ∑ q : OrdinaryPairing r,
      ordinaryPairingDelta p i *
        ((N : ℝ) ^ r * (ordinaryPairingGram (Fin N) r)⁻¹ p q -
          (if p = q then (1 : ℝ) else 0)) * ordinaryPairingDelta q j := by
  rw [entryMoment_eq_weingarten_delta_sum (by simpa only [Fintype.card_fin] using hr)]
  simp_rw [mul_sub, sub_mul, Finset.sum_sub_distrib]
  congr 1
  · simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    ring
  · simp

/-- One eventual dimension threshold gives the genuine leading matching-pairing
approximation for ALL row and column tuples, with explicit reciprocal error. -/
theorem eventually_rescaled_entryMoment_error_le (r : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ i j : Fin (2 * r) → Fin N,
      |(N : ℝ) ^ r * entryMoment i j -
        ∑ p : OrdinaryPairing r, ordinaryPairingDelta p i * ordinaryPairingDelta p j|
      ≤ 2 * (Fintype.card (OrdinaryPairing r) : ℝ) ^ 3 / (N : ℝ) := by
  filter_upwards [eventually_ge_atTop r, eventually_ge_atTop 1,
    eventually_rescaledWeingartenWeight_error_le r] with N hr hN hb
  intro i j
  rw [rescaled_entryMoment_sub_pairing_sum hr]
  let C : ℝ := 2 * (Fintype.card (OrdinaryPairing r) : ℝ) / (N : ℝ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    |∑ p : OrdinaryPairing r, ∑ q : OrdinaryPairing r, _| ≤
        ∑ p : OrdinaryPairing r, ∑ q : OrdinaryPairing r,
          |ordinaryPairingDelta p i *
            ((N : ℝ) ^ r * (ordinaryPairingGram (Fin N) r)⁻¹ p q -
              (if p = q then (1 : ℝ) else 0)) * ordinaryPairingDelta q j| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      exact Finset.sum_le_sum (fun p _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _p : OrdinaryPairing r, ∑ _q : OrdinaryPairing r, C := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro q _
      rw [abs_mul, abs_mul]
      calc
        _ ≤ (1 * C) * 1 :=
          mul_le_mul (mul_le_mul (ordinaryPairingDelta_abs_le_one p i) (hb p q)
            (abs_nonneg _) (by norm_num)) (ordinaryPairingDelta_abs_le_one q j)
            (abs_nonneg _) (by simpa using hC)
        _ = C := by ring
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      dsimp [C]
      ring

end FreeProbability.Orthogonal

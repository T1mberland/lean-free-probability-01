import FreeProbability.RandomMatrix.OrthogonalPairingLoopBounds
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Genuine normalized Gram and leading Weingarten limits -/

noncomputable section
open scoped Classical Topology
namespace FreeProbability.Orthogonal
open Filter Matrix

/-- The true dimension-normalized ordinary pairing Gram matrix. -/
def normalizedPairingGram (r N : ℕ) : Matrix (OrdinaryPairing r) (OrdinaryPairing r) ℝ :=
  ((N : ℝ) ^ r)⁻¹ • ordinaryPairingGram (Fin N) r

theorem normalizedPairingGram_apply (r N : ℕ) (p q : OrdinaryPairing r) :
    normalizedPairingGram r N p q = ((N : ℝ) ^ r)⁻¹ * (N : ℝ) ^ pairingLoopCount p q := by
  change ((N : ℝ) ^ r)⁻¹ * (Fintype.card (Fin N) : ℝ) ^ pairingLoopCount p q = _
  rw [Fintype.card_fin]

private theorem normalized_power_eq (x : ℝ) (hx : x ≠ 0) (c r : ℕ) (hcr : c ≤ r) :
    (x ^ r)⁻¹ * x ^ c = (x⁻¹) ^ (r - c) := by
  conv_lhs => rw [show r = c + (r - c) by omega, pow_add]
  simp only [_root_.mul_inv_rev, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hx), mul_one, inv_pow]

/-- The ACTUAL normalized Gram matrices converge to the identity as the
coordinate dimension tends to infinity. -/
theorem tendsto_normalizedPairingGram (r : ℕ) :
    Tendsto (normalizedPairingGram r) atTop (𝓝 (1 : Matrix (OrdinaryPairing r) (OrdinaryPairing r) ℝ)) := by
  apply tendsto_pi_nhds.mpr
  intro p
  apply tendsto_pi_nhds.mpr
  intro q
  simp only [Matrix.one_apply]
  have hlarge : ∀ᶠ N : ℕ in atTop, 1 ≤ N := eventually_ge_atTop 1
  have he : (fun N => normalizedPairingGram r N p q) =ᶠ[atTop]
      (fun N => ((N : ℝ)⁻¹) ^ (r - pairingLoopCount p q)) := by
    filter_upwards [hlarge] with N hN
    rw [normalizedPairingGram_apply]
    exact normalized_power_eq _ (by exact_mod_cast (show N ≠ 0 by omega)) _ _ (pairingLoopCount_le p q)
  by_cases hpq : p = q
  · subst q
    have hc := (pairingLoopCount_eq_iff p p).mpr rfl
    simp only [ite_true]
    apply tendsto_const_nhds.congr'
    simpa only [hc, Nat.sub_self, pow_zero] using he.symm
  · simp only [hpq, ite_false]
    have hd : r - pairingLoopCount p q ≠ 0 := by have h := pairingLoopCount_lt_of_ne p q hpq; omega
    have hi : Tendsto (fun N : ℕ => ((N : ℝ)⁻¹)) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have h := hi.pow (r - pairingLoopCount p q)
    simp only [zero_pow hd] at h
    exact h.congr' he.symm

/-- Continuity of the LITERAL nonsingular matrix inverse yields the true
normalized inverse limit. -/
theorem tendsto_normalizedPairingGram_inverse (r : ℕ) :
    Tendsto (fun N : ℕ => (normalizedPairingGram r N)⁻¹) atTop
      (𝓝 (1 : Matrix (OrdinaryPairing r) (OrdinaryPairing r) ℝ)) := by
  have hc := continuousAt_matrix_inv (1 : Matrix (OrdinaryPairing r) (OrdinaryPairing r) ℝ)
    (by simp only [Matrix.det_one, Ring.inverse_eq_inv']; exact continuousAt_inv₀ (by norm_num))
  simpa only [inv_one, Function.comp_def] using hc.tendsto.comp (tendsto_normalizedPairingGram r)

/-- In stable nonzero dimension, the inverse of the actual normalized Gram
is exactly the dimension-rescaled TRUE Weingarten matrix. -/
theorem normalizedPairingGram_inverse_eq (r N : ℕ) (hr : r ≤ N) (hN : N ≠ 0) :
    (normalizedPairingGram r N)⁻¹ = (N : ℝ) ^ r • (ordinaryPairingGram (Fin N) r)⁻¹ := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  let : Invertible (((N : ℝ) ^ r)⁻¹) := invertibleOfNonzero (inv_ne_zero (pow_ne_zero r hNr))
  have hd : IsUnit (ordinaryPairingGram (Fin N) r).det :=
    isUnit_iff_ne_zero.mpr (ordinaryPairingGram_det_ne_zero r (by simpa only [Fintype.card_fin] using hr))
  rw [normalizedPairingGram, Matrix.inv_smul _ _ hd]
  simp only [invOf_eq_inv, inv_inv]

/-- The GENUINE Weingarten matrix has its dimension-rescaled leading limit I. -/
theorem tendsto_rescaledPairingGram_inverse (r : ℕ) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ r • (ordinaryPairingGram (Fin N) r)⁻¹) atTop
      (𝓝 (1 : Matrix (OrdinaryPairing r) (OrdinaryPairing r) ℝ)) := by
  apply (tendsto_normalizedPairingGram_inverse r).congr'
  filter_upwards [eventually_ge_atTop (max r 1)] with N hN
  exact normalizedPairingGram_inverse_eq r N (le_max_left r 1 |>.trans hN) (by omega)

/-- Every actual stable Weingarten weight has the proved leading asymptotic:
N^r times its entry tends to the intrinsic pairing Kronecker delta. -/
theorem tendsto_rescaledWeingartenWeight (r : ℕ) (p q : OrdinaryPairing r) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ r * (ordinaryPairingGram (Fin N) r)⁻¹ p q)
      atTop (𝓝 (if p = q then (1 : ℝ) else 0)) := by
  have h := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (tendsto_rescaledPairingGram_inverse r) p) q
  change Tendsto (fun N : ℕ => (N : ℝ) ^ r * (ordinaryPairingGram (Fin N) r)⁻¹ p q)
    atTop (𝓝 ((1 : Matrix (OrdinaryPairing r) (OrdinaryPairing r) ℝ) p q)) at h
  simpa only [Matrix.one_apply] using h
end FreeProbability.Orthogonal

import FreeProbability.RandomMatrix.OrthogonalPairingRowTransfer
import FreeProbability.RandomMatrix.OrthogonalPermutationCycleBound
import FreeProbability.RandomMatrix.OrthogonalWeingartenDistanceBounds

/-! # Genuine expected centered single-Haar trace bounds -/

noncomputable section
open scoped Classical Topology
namespace FreeProbability.Orthogonal
open Matrix Filter
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A nonzero ACTUAL centered paired network cannot have singleton cycles;
its genuine raw loop count is therefore at most half its edge count. -/
theorem centered_pairingNetwork_nonzero_loop_bound {r : ℕ} (p : OrdinaryPairing r)
    (e : PairingSites r) (M : Fin r → Matrix n n ℂ) (hM : ∀ k, Matrix.trace (M k) = 0)
    (hne : pairingNetwork p e M ≠ 0) : 2 * pairingLoopCount p (Quotient.mk _ e) ≤ r := by
  have hf : ∀ a : PairingHalfSites p (Quotient.mk _ e),
      pairingHalfPermutation p (Quotient.mk _ e) a ≠ a := by
    intro a ha
    exact hne (pairingNetwork_eq_zero_of_centered_fixed_cycle p e M hM a ha)
  have h := twice_permutationOrbit_card_le (pairingHalfPermutation p (Quotient.mk _ e)) hf
  rwa [pairingHalf_orbit_card, pairingHalfSites_card] at h

private theorem inv_mul_power (x : ℝ) (hx : x ≠ 0) {r : ℕ} (hr : 0 < r) :
    x⁻¹ * x ^ r = x ^ (r - 1) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  rw [pow_succ', ← mul_assoc, inv_mul_cancel₀ hx, one_mul]
  rfl

/-- Actual centered trace-word contractions have the genuine dimension power
r-1. Every deterministic factor is centered; positive word length is explicit. -/
theorem centered_tracePairingContraction_norm_le {r : ℕ} (hr : 0 < r)
    (hn : 0 < Fintype.card n) (A B : Fin r → Matrix n n ℂ)
    (hA : ∀ k, Matrix.trace (A k) = 0) (hB : ∀ k, Matrix.trace (B k) = 0)
    (p q : OrdinaryPairing r) :
    ‖tracePairingContraction A B p q‖ ≤ (Fintype.card n : ℝ) ^ (r - 1) *
      (∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A k)‖) *
      (∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B k)‖) := by
  rw [tracePairingContraction_eq_network_product hr]
  by_cases hR : traceRowNetwork B p = 0
  · rw [hR, mul_zero, zero_mul, norm_zero]; positivity
  by_cases hC : traceColumnNetwork A q = 0
  · rw [hC, mul_zero, norm_zero]; positivity
  have hRB : pairingNetwork p (traceRowEdgeCode r) B ≠ 0 := by
    rwa [← traceRowNetwork_eq_pairingNetwork]
  have hCA : pairingNetwork q (traceColumnEdgeCode r) A ≠ 0 := by
    rwa [← traceColumnNetwork_eq_pairingNetwork]
  have hrl := centered_pairingNetwork_nonzero_loop_bound p _ B hB hRB
  have hcl := centered_pairingNetwork_nonzero_loop_bound q _ A hA hCA
  have hs : pairingLoopCount p (Quotient.mk _ (traceRowEdgeCode r)) +
      pairingLoopCount q (Quotient.mk _ (traceColumnEdgeCode r)) ≤ r := by omega
  have hN1 : (1 : ℝ) ≤ Fintype.card n := by exact_mod_cast hn
  have hN0 : (Fintype.card n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hi : ‖(Fintype.card n : ℂ)⁻¹‖ = (Fintype.card n : ℝ)⁻¹ := by simp
  rw [norm_mul, norm_mul, hi]
  calc
    _ ≤ ((Fintype.card n : ℝ)⁻¹ *
        ((Fintype.card n : ℝ) ^ pairingLoopCount p (Quotient.mk _ (traceRowEdgeCode r)) *
          ∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B k)‖)) *
        ((Fintype.card n : ℝ) ^ pairingLoopCount q (Quotient.mk _ (traceColumnEdgeCode r)) *
          ∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A k)‖) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (traceRowNetwork_norm_le B p) (by positivity))
        (traceColumnNetwork_norm_le A q) (norm_nonneg _) (by positivity)
    _ = ((Fintype.card n : ℝ)⁻¹ * (Fintype.card n : ℝ) ^
        (pairingLoopCount p (Quotient.mk _ (traceRowEdgeCode r)) +
          pairingLoopCount q (Quotient.mk _ (traceColumnEdgeCode r)))) *
        (∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A k)‖) *
        (∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B k)‖) := by rw [pow_add]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      calc
        _ ≤ (Fintype.card n : ℝ)⁻¹ * (Fintype.card n : ℝ) ^ r :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hN1 hs) (by positivity)
        _ = _ := inv_mul_power _ hN0 hr

/-- An explicit degree-dependent constant for the actual centered expectation bound. -/
def orthogonalCenteredTraceConstant (r : ℕ) : ℝ :=
  (Fintype.card (OrdinaryPairing r) : ℝ) ^ 2 *
    ((r : ℝ) * (Fintype.card (OrdinaryPairing r) : ℝ) ^ r +
      2 * (Fintype.card (OrdinaryPairing r) : ℝ) ^ (r + 1))

private theorem reciprocal_power_cancel (x : ℝ) (hx : x ≠ 0) {r : ℕ} (hr : 0 < r) :
    (x⁻¹) ^ r * x ^ (r - 1) = x⁻¹ := by
  rw [← inv_mul_power x hx hr]
  calc
    _ = x⁻¹ * ((x⁻¹) ^ r * x ^ r) := by ring
    _ = x⁻¹ := by rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero r hx), mul_one]

/-- The GENUINE expected normalized centered single-Haar cyclic trace has
reciprocal-dimension decay, uniformly for ALL deterministic complex factors.
The threshold depends only on the positive word length. -/
theorem eventually_centered_traceWordMoment_norm_le {r : ℕ} (hr : 0 < r) :
    ∀ᶠ N : ℕ in atTop, ∀ A B : Fin r → Matrix (Fin N) (Fin N) ℂ,
      (∀ k, Matrix.trace (A k) = 0) → (∀ k, Matrix.trace (B k) = 0) →
      ‖traceWordMoment A B‖ ≤ orthogonalCenteredTraceConstant r / (N : ℝ) *
        (∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A k)‖) *
        (∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B k)‖) := by
  filter_upwards [eventually_ge_atTop (max r 1),
    eventually_rescaledWeingartenWeight_distance_bound r] with N hN hb
  intro A B hA hB
  have hN1 : 1 ≤ N := le_max_right r 1 |>.trans hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  let C : ℝ := (r : ℝ) * (Fintype.card (OrdinaryPairing r) : ℝ) ^ r +
    2 * (Fintype.card (OrdinaryPairing r) : ℝ) ^ (r + 1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hw (p q : OrdinaryPairing r) :
      ‖((ordinaryPairingGram (Fin N) r)⁻¹ p q : ℂ)‖ ≤ C * ((N : ℝ)⁻¹) ^ r := by
    have he := (hb p q).trans (mul_le_of_le_one_right hC
      (pow_le_one₀ (by positivity) ((inv_le_one₀ hNr).mpr hNr1)))
    rw [abs_mul, abs_of_pos (pow_pos hNr r)] at he
    have hd : |(ordinaryPairingGram (Fin N) r)⁻¹ p q| ≤ C / (N : ℝ) ^ r :=
      (le_div_iff₀ (pow_pos hNr r)).mpr (by simpa only [mul_comm] using he)
    simpa only [Complex.norm_real, Real.norm_eq_abs, div_eq_mul_inv, inv_pow] using hd
  have hterm (p q : OrdinaryPairing r) :
      ‖((ordinaryPairingGram (Fin N) r)⁻¹ p q : ℂ) * tracePairingContraction A B p q‖ ≤
      C / (N : ℝ) * (∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A k)‖) *
        (∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B k)‖) := by
    rw [norm_mul]
    have hc := centered_tracePairingContraction_norm_le hr
      (by simpa only [Fintype.card_fin] using (show 0 < N by omega)) A B hA hB p q
    calc
      _ ≤ (C * ((N : ℝ)⁻¹) ^ r) * ((N : ℝ) ^ (r - 1) *
          (∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A k)‖) *
          (∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B k)‖)) :=
        mul_le_mul (hw p q) (by simpa only [Fintype.card_fin] using hc) (norm_nonneg _) (by positivity)
      _ = _ := by
        have he := reciprocal_power_cancel (N : ℝ) hNr.ne' hr
        calc
          _ = C * (((N : ℝ)⁻¹) ^ r * (N : ℝ) ^ (r - 1)) *
              (∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A k)‖) *
              (∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B k)‖) := by ring
          _ = _ := by rw [he, div_eq_mul_inv]
  rw [traceWordMoment_eq_weingarten_contractions
    (by simpa only [Fintype.card_fin] using (le_max_left r 1 |>.trans hN))]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ p : OrdinaryPairing r, ∑ q : OrdinaryPairing r,
        ‖((ordinaryPairingGram (Fin N) r)⁻¹ p q : ℂ) * tracePairingContraction A B p q‖ :=
      Finset.sum_le_sum (fun p _ => norm_sum_le _ _)
    _ ≤ ∑ _p : OrdinaryPairing r, ∑ _q : OrdinaryPairing r,
        C / (N : ℝ) * (∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A k)‖) *
          (∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B k)‖) :=
      Finset.sum_le_sum (fun p _ => Finset.sum_le_sum (fun q _ => hterm p q))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      unfold orthogonalCenteredTraceConstant
      dsimp [C]
      ring

/-- Uniform actual expected trace decay under a genuine bound on EVERY
Euclidean operator norm. No variance or almost-sure conclusion is asserted. -/
theorem eventually_centered_traceWordMoment_uniform_bound {r : ℕ} (hr : 0 < r)
    (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ N : ℕ in atTop, ∀ A B : Fin r → Matrix (Fin N) (Fin N) ℂ,
      (∀ k, Matrix.trace (A k) = 0) → (∀ k, Matrix.trace (B k) = 0) →
      (∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A k)‖ ≤ K) →
      (∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B k)‖ ≤ K) →
      ‖traceWordMoment A B‖ ≤ orthogonalCenteredTraceConstant r * K ^ (2 * r) / (N : ℝ) := by
  filter_upwards [eventually_centered_traceWordMoment_norm_le hr, eventually_ge_atTop 1] with N hN hpos
  intro A B hA hB hAn hBn
  have hpA : (∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A k)‖) ≤ K ^ r := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      Finset.prod_le_prod₀ (s := Finset.univ) (fun k _ => norm_nonneg _) (fun k _ => hAn k)
  have hpB : (∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B k)‖) ≤ K ^ r := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      Finset.prod_le_prod₀ (s := Finset.univ) (fun k _ => norm_nonneg _) (fun k _ => hBn k)
  have hC : 0 ≤ orthogonalCenteredTraceConstant r / (N : ℝ) := by
    unfold orthogonalCenteredTraceConstant
    positivity
  calc
    _ ≤ orthogonalCenteredTraceConstant r / (N : ℝ) *
        (∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A k)‖) *
        (∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B k)‖) := hN A B hA hB
    _ ≤ orthogonalCenteredTraceConstant r / (N : ℝ) * K ^ r * K ^ r :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpA hC) hpB (by positivity) (by positivity)
    _ = _ := by rw [show 2 * r = r + r by omega, pow_add]; ring

/-- Genuine expected centered single-Haar normalized traces tend to zero for
uniformly operator-bounded deterministic matrix families. -/
theorem tendsto_centered_traceWordMoment {r : ℕ} (hr : 0 < r) (K : ℝ) (hK : 0 ≤ K)
    (A B : ∀ N : ℕ, Fin r → Matrix (Fin N) (Fin N) ℂ)
    (hA : ∀ N k, Matrix.trace (A N k) = 0) (hB : ∀ N k, Matrix.trace (B N k) = 0)
    (hAn : ∀ N k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A N k)‖ ≤ K)
    (hBn : ∀ N k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B N k)‖ ≤ K) :
    Tendsto (fun N => traceWordMoment (A N) (B N)) atTop (𝓝 0) := by
  have hb : ∀ᶠ N : ℕ in atTop, ‖traceWordMoment (A N) (B N)‖ ≤
      orthogonalCenteredTraceConstant r * K ^ (2 * r) / (N : ℝ) := by
    filter_upwards [eventually_centered_traceWordMoment_uniform_bound hr K hK] with N hN
    exact hN (A N) (B N) (hA N) (hB N) (hAn N) (hBn N)
  apply squeeze_zero_norm' hb
  have hi : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  simpa only [div_eq_mul_inv, mul_zero] using
    tendsto_const_nhds.mul (f := fun _ : ℕ => orthogonalCenteredTraceConstant r * K ^ (2 * r)) hi

end FreeProbability.Orthogonal

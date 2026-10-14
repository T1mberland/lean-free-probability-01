import FreeProbability.RandomMatrix.OrthogonalMultiTraceContractions

/-! # Genuine centered multi-trace expectation bounds -/

noncomputable section
open scoped Classical Topology
namespace FreeProbability.Orthogonal
open Matrix Filter Equiv.Perm
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- All actual trace cycles are nonempty, so their number is at most the number
of factors. Singleton cycles are included. -/
theorem multiTraceCount_le {r : ℕ} (π : Equiv.Perm (Fin r)) :
    Fintype.card (PermutationOrbitIndex π) ≤ r := by
  simpa only [Fintype.card_fin] using Fintype.card_quotient_le (SameCycle.setoid π)

theorem multiTraceCount_pos {r : ℕ} (hr : 0 < r) (π : Equiv.Perm (Fin r)) :
    0 < Fintype.card (PermutationOrbitIndex π) :=
  Fintype.card_pos_iff.mpr ⟨Quotient.mk _ ⟨0, hr⟩⟩

private theorem inverse_power_product (x : ℝ) (hx : x ≠ 0) (r m : ℕ) (hm : m ≤ r) :
    (x⁻¹) ^ m * x ^ r = x ^ (r - m) := by
  have he : x ^ r = x ^ m * x ^ (r - m) := by rw [← pow_add]; congr 1; omega
  rw [he, inv_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero m hx), one_mul]

/-- Actual centered multi-trace contractions have power N^(r-m), with m the
number of genuine nonempty trace cycles. No cycle-count bound is assumed. -/
theorem centered_multiTracePairingContraction_norm_le {r : ℕ}
    (hn : 0 < Fintype.card n) (π : Equiv.Perm (Fin r)) (A B : Fin r → Matrix n n ℂ)
    (hA : ∀ k, Matrix.trace (A k) = 0) (hB : ∀ k, Matrix.trace (B k) = 0)
    (p q : OrdinaryPairing r) :
    ‖multiTracePairingContraction π A B p q‖ ≤
      (Fintype.card n : ℝ) ^ (r - Fintype.card (PermutationOrbitIndex π)) *
        (∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A k)‖) *
        (∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B k)‖) := by
  rw [multiTracePairingContraction_eq_network_product]
  by_cases hR : multiTraceRowNetwork π B p = 0
  · rw [hR, mul_zero, zero_mul, norm_zero]; positivity
  by_cases hC : traceColumnNetwork A q = 0
  · rw [hC, mul_zero, norm_zero]; positivity
  have hRB : pairingNetwork p (multiTraceRowEdgeCode π) B ≠ 0 := by
    rwa [← multiTraceRowNetwork_eq_pairingNetwork]
  have hCA : pairingNetwork q (traceColumnEdgeCode r) A ≠ 0 := by
    rwa [← traceColumnNetwork_eq_pairingNetwork]
  have hrl := centered_pairingNetwork_nonzero_loop_bound p _ B hB hRB
  have hcl := centered_pairingNetwork_nonzero_loop_bound q _ A hA hCA
  have hs : pairingLoopCount p (Quotient.mk _ (multiTraceRowEdgeCode π)) +
      pairingLoopCount q (Quotient.mk _ (traceColumnEdgeCode r)) ≤ r := by omega
  have hN1 : (1 : ℝ) ≤ Fintype.card n := by exact_mod_cast hn
  have hN0 : (Fintype.card n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hi : ‖((Fintype.card n : ℂ)⁻¹) ^ Fintype.card (PermutationOrbitIndex π)‖ =
      ((Fintype.card n : ℝ)⁻¹) ^ Fintype.card (PermutationOrbitIndex π) := by simp
  rw [norm_mul, norm_mul, hi]
  calc
    _ ≤ ((((Fintype.card n : ℝ)⁻¹) ^ Fintype.card (PermutationOrbitIndex π)) *
        ((Fintype.card n : ℝ) ^ pairingLoopCount p (Quotient.mk _ (multiTraceRowEdgeCode π)) *
          ∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B k)‖)) *
        ((Fintype.card n : ℝ) ^ pairingLoopCount q (Quotient.mk _ (traceColumnEdgeCode r)) *
          ∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A k)‖) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (multiTraceRowNetwork_norm_le π B p) (by positivity))
        (traceColumnNetwork_norm_le A q) (norm_nonneg _) (by positivity)
    _ = ((((Fintype.card n : ℝ)⁻¹) ^ Fintype.card (PermutationOrbitIndex π)) *
        (Fintype.card n : ℝ) ^
          (pairingLoopCount p (Quotient.mk _ (multiTraceRowEdgeCode π)) +
            pairingLoopCount q (Quotient.mk _ (traceColumnEdgeCode r)))) *
        (∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A k)‖) *
        (∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B k)‖) := by rw [pow_add]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      calc
        _ ≤ (((Fintype.card n : ℝ)⁻¹) ^ Fintype.card (PermutationOrbitIndex π)) *
            (Fintype.card n : ℝ) ^ r := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hN1 hs) (by positivity)
        _ = _ := inverse_power_product _ hN0 r _ (multiTraceCount_le π)

private theorem reciprocal_power_compensate (x : ℝ) (hx : x ≠ 0) (r m : ℕ) (hm : m ≤ r) :
    (x⁻¹) ^ r * x ^ (r - m) = (x⁻¹) ^ m := by
  have he : x ^ r = x ^ m * x ^ (r - m) := by rw [← pow_add]; congr 1; omega
  calc
    _ = (x ^ m)⁻¹ * ((x ^ (r - m))⁻¹ * x ^ (r - m)) := by rw [inv_pow, he, _root_.mul_inv_rev]; ring
    _ = _ := by rw [inv_mul_cancel₀ (pow_ne_zero _ hx), mul_one, inv_pow]

/-- Genuine actual expected products of m normalized centered traces decay
as N^-m. One threshold works for ALL trace permutations and matrices at fixed r. -/
theorem eventually_centered_multiTraceWordMoment_norm_le (r : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ (π : Equiv.Perm (Fin r)) (A B : Fin r → Matrix (Fin N) (Fin N) ℂ),
      (∀ k, Matrix.trace (A k) = 0) → (∀ k, Matrix.trace (B k) = 0) →
      ‖multiTraceWordMoment π A B‖ ≤ orthogonalCenteredTraceConstant r *
        ((N : ℝ)⁻¹) ^ Fintype.card (PermutationOrbitIndex π) *
        (∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A k)‖) *
        (∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B k)‖) := by
  filter_upwards [eventually_ge_atTop (max r 1),
    eventually_rescaledWeingartenWeight_distance_bound r] with N hN hb
  intro π A B hA hB
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
      ‖((ordinaryPairingGram (Fin N) r)⁻¹ p q : ℂ) * multiTracePairingContraction π A B p q‖ ≤
      C * ((N : ℝ)⁻¹) ^ Fintype.card (PermutationOrbitIndex π) *
        (∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A k)‖) *
        (∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B k)‖) := by
    rw [norm_mul]
    have hc := centered_multiTracePairingContraction_norm_le
      (by simpa only [Fintype.card_fin] using (show 0 < N by omega)) π A B hA hB p q
    calc
      _ ≤ (C * ((N : ℝ)⁻¹) ^ r) * ((N : ℝ) ^ (r - Fintype.card (PermutationOrbitIndex π)) *
          (∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A k)‖) *
          (∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B k)‖)) :=
        mul_le_mul (hw p q) (by simpa only [Fintype.card_fin] using hc) (norm_nonneg _) (by positivity)
      _ = _ := by
        have he := reciprocal_power_compensate (N : ℝ) hNr.ne' r _ (multiTraceCount_le π)
        calc
          _ = C * (((N : ℝ)⁻¹) ^ r * (N : ℝ) ^ (r - Fintype.card (PermutationOrbitIndex π))) *
              (∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A k)‖) *
              (∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B k)‖) := by ring
          _ = _ := by rw [he]
  rw [multiTraceWordMoment_eq_weingarten_contractions
    (by simpa only [Fintype.card_fin] using (le_max_left r 1 |>.trans hN))]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ p : OrdinaryPairing r, ∑ q : OrdinaryPairing r,
        ‖((ordinaryPairingGram (Fin N) r)⁻¹ p q : ℂ) * multiTracePairingContraction π A B p q‖ :=
      Finset.sum_le_sum (fun p _ => norm_sum_le _ _)
    _ ≤ ∑ _p : OrdinaryPairing r, ∑ _q : OrdinaryPairing r,
        C * ((N : ℝ)⁻¹) ^ Fintype.card (PermutationOrbitIndex π) *
          (∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A k)‖) *
          (∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B k)‖) :=
      Finset.sum_le_sum (fun p _ => Finset.sum_le_sum (fun q _ => hterm p q))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      unfold orthogonalCenteredTraceConstant
      dsimp [C]
      ring

/-- Uniform genuine multi-trace decay with a common actual operator bound. -/
theorem eventually_centered_multiTraceWordMoment_uniform_bound (r : ℕ) (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ N : ℕ in atTop, ∀ (π : Equiv.Perm (Fin r)) (A B : Fin r → Matrix (Fin N) (Fin N) ℂ),
      (∀ k, Matrix.trace (A k) = 0) → (∀ k, Matrix.trace (B k) = 0) →
      (∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A k)‖ ≤ K) →
      (∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B k)‖ ≤ K) →
      ‖multiTraceWordMoment π A B‖ ≤ orthogonalCenteredTraceConstant r * K ^ (2 * r) *
        ((N : ℝ)⁻¹) ^ Fintype.card (PermutationOrbitIndex π) := by
  filter_upwards [eventually_centered_multiTraceWordMoment_norm_le r] with N hN
  intro π A B hA hB hAn hBn
  have hpA : (∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A k)‖) ≤ K ^ r := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      Finset.prod_le_prod₀ (s := Finset.univ) (fun k _ => norm_nonneg _) (fun k _ => hAn k)
  have hpB : (∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B k)‖) ≤ K ^ r := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      Finset.prod_le_prod₀ (s := Finset.univ) (fun k _ => norm_nonneg _) (fun k _ => hBn k)
  have hC : 0 ≤ orthogonalCenteredTraceConstant r * ((N : ℝ)⁻¹) ^ Fintype.card (PermutationOrbitIndex π) := by
    unfold orthogonalCenteredTraceConstant
    positivity
  calc
    _ ≤ orthogonalCenteredTraceConstant r * ((N : ℝ)⁻¹) ^ Fintype.card (PermutationOrbitIndex π) *
        (∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A k)‖) *
        (∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B k)‖) := hN π A B hA hB
    _ ≤ orthogonalCenteredTraceConstant r * ((N : ℝ)⁻¹) ^ Fintype.card (PermutationOrbitIndex π) * K ^ r * K ^ r :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpA hC) hpB (by positivity) (by positivity)
    _ = _ := by rw [show 2 * r = r + r by omega, pow_add]; ring

/-- Actual nonempty centered multi-trace expectations tend to zero under
genuine uniform operator bounds. No probabilistic convergence mode is inferred. -/
theorem tendsto_centered_multiTraceWordMoment {r : ℕ} (hr : 0 < r)
    (π : Equiv.Perm (Fin r)) (K : ℝ) (hK : 0 ≤ K)
    (A B : ∀ N : ℕ, Fin r → Matrix (Fin N) (Fin N) ℂ)
    (hA : ∀ N k, Matrix.trace (A N k) = 0) (hB : ∀ N k, Matrix.trace (B N k) = 0)
    (hAn : ∀ N k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A N k)‖ ≤ K)
    (hBn : ∀ N k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B N k)‖ ≤ K) :
    Tendsto (fun N => multiTraceWordMoment π (A N) (B N)) atTop (𝓝 0) := by
  have hb : ∀ᶠ N : ℕ in atTop, ‖multiTraceWordMoment π (A N) (B N)‖ ≤
      orthogonalCenteredTraceConstant r * K ^ (2 * r) *
        ((N : ℝ)⁻¹) ^ Fintype.card (PermutationOrbitIndex π) := by
    filter_upwards [eventually_centered_multiTraceWordMoment_uniform_bound r K hK] with N hN
    exact hN π (A N) (B N) (hA N) (hB N) (hAn N) (hBn N)
  apply squeeze_zero_norm' hb
  have hi : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hp := hi.pow (Fintype.card (PermutationOrbitIndex π))
  rw [zero_pow (Nat.ne_of_gt (multiTraceCount_pos hr π))] at hp
  simpa only [mul_zero] using
    tendsto_const_nhds.mul (f := fun _ : ℕ => orthogonalCenteredTraceConstant r * K ^ (2 * r)) hp

end FreeProbability.Orthogonal

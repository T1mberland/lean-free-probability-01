import FreeProbability.Algebraic.CumulantRCLikeFreeCLT

/-!
# Quantitative free triangular-array cumulant estimates

The summands need not have identical marginal laws. Each fixed higher-order
marginal cumulant is bounded uniformly in the row and summand; the resulting
inverse-square-root normalized cumulant tends to zero.
-/

namespace FreeProbability

open Filter Topology

theorem freeCLT_normalization_coefficient_tendsto {k : ℕ} (hk : 2 ≤ k) :
    Tendsto (fun N : ℕ => (Real.sqrt (N : ℝ))⁻¹ ^ k * (N : ℝ)) atTop
      (𝓝 (if k = 2 then 1 else 0)) := by
  have he (N : ℕ) (hN : 0 < N) :
      (Real.sqrt (N : ℝ))⁻¹ ^ k * (N : ℝ) = (Real.sqrt (N : ℝ))⁻¹ ^ (k - 2) := by
    have hs : Real.sqrt (N : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hN))
    have hsq : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
    have hc : (Real.sqrt (N : ℝ))⁻¹ ^ 2 * (N : ℝ) = 1 := by
      calc
        (Real.sqrt (N : ℝ))⁻¹ ^ 2 * (N : ℝ) =
            (Real.sqrt (N : ℝ))⁻¹ ^ 2 * Real.sqrt (N : ℝ) ^ 2 := congrArg _ hsq.symm
        _ = 1 := by rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hs)]
    calc
      (Real.sqrt (N : ℝ))⁻¹ ^ k * (N : ℝ) =
          (Real.sqrt (N : ℝ))⁻¹ ^ ((k - 2) + 2) * (N : ℝ) := by congr 2; omega
      _ = (Real.sqrt (N : ℝ))⁻¹ ^ (k - 2) * ((Real.sqrt (N : ℝ))⁻¹ ^ 2 * (N : ℝ)) :=
        by rw [pow_add, mul_assoc]
      _ = (Real.sqrt (N : ℝ))⁻¹ ^ (k - 2) := by rw [hc, mul_one]
  have hevent : (fun N : ℕ => (Real.sqrt (N : ℝ))⁻¹ ^ k * (N : ℝ)) =ᶠ[atTop]
      (fun N : ℕ => (Real.sqrt (N : ℝ))⁻¹ ^ (k - 2)) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact he N (by omega)
  by_cases hk2 : k = 2
  · subst k
    simp only [Nat.sub_self, pow_zero] at hevent
    exact tendsto_const_nhds.congr' hevent.symm
  have hc : Tendsto (fun N : ℕ => (Real.sqrt (N : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hpow : Tendsto (fun N : ℕ => (Real.sqrt (N : ℝ))⁻¹ ^ (k - 2)) atTop (𝓝 0) := by
    simpa only [zero_pow (by omega : k - 2 ≠ 0)] using hc.pow (k - 2)
  simpa only [hk2, ite_false] using hpow.congr' hevent.symm


variable {𝕜 : Type*} [RCLike 𝕜]

/-- A uniform fixed-order marginal cumulant bound gives an explicit normalized
free-sum cumulant bound, without identical distribution. -/
theorem FreelyIndependent.norm_cumulant_normalized_sum_le {D : Type*} [Ring D] [Algebra 𝕜 D]
    {N : ℕ} {φ : ProbabilitySpace 𝕜 D} {B : Fin N → Subalgebra 𝕜 D}
    (hfree : FreelyIndependent φ B) (a : Fin N → D) (ha : ∀ i, a i ∈ B i)
    (k : ℕ) (C : ℝ) (hbound : ∀ i, ‖cumulant φ (List.replicate k (a i))‖ ≤ C) :
    ‖cumulant φ (List.replicate k (((Real.sqrt (N : ℝ))⁻¹ : 𝕜) • ∑ i, a i))‖ ≤
      ((Real.sqrt (N : ℝ))⁻¹ ^ k * (N : ℝ)) * C := by
  classical
  rw [cumulant_replicate_smul, hfree.cumulant_replicate_sum a ha, norm_mul, norm_pow,
    norm_inv, RCLike.norm_ofReal, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hsum : ‖∑ i, cumulant φ (List.replicate k (a i))‖ ≤ (N : ℝ) * C := by
    calc
      _ ≤ ∑ i : Fin N, ‖cumulant φ (List.replicate k (a i))‖ := norm_sum_le _ _
      _ ≤ ∑ _ : Fin N, C := Finset.sum_le_sum (fun i _ => hbound i)
      _ = (N : ℝ) * C := by simp
  calc
    _ ≤ (Real.sqrt (N : ℝ))⁻¹ ^ k * ((N : ℝ) * C) :=
      mul_le_mul_of_nonneg_left hsum (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _)
    _ = _ := (mul_assoc _ _ _).symm

/-- Uniform higher-order marginal cumulant bounds force the normalized free
triangular-array cumulants to vanish at every order greater than two. -/
theorem freeCLT_triangular_higher_cumulants {D : ℕ → Type*} [∀ N, Ring (D N)]
    [∀ N, Algebra 𝕜 (D N)] (φ : ∀ N, ProbabilitySpace 𝕜 (D N))
    (B : ∀ N, Fin N → Subalgebra 𝕜 (D N)) (a : ∀ N, Fin N → D N)
    (hfree : ∀ N, FreelyIndependent (φ N) (B N)) (hmem : ∀ N i, a N i ∈ B N i)
    (k : ℕ) (hk : 2 < k) (C : ℝ)
    (hbound : ∀ N i, ‖cumulant (φ N) (List.replicate k (a N i))‖ ≤ C) :
    Tendsto (fun N => cumulant (φ N)
      (List.replicate k (((Real.sqrt (N : ℝ))⁻¹ : 𝕜) • ∑ i, a N i))) atTop (𝓝 0) := by
  apply squeeze_zero_norm
    (fun N => (hfree N).norm_cumulant_normalized_sum_le (a N) (hmem N) k C (hbound N))
  have h := (freeCLT_normalization_coefficient_tendsto (by omega : 2 ≤ k)).mul_const C
  simpa only [ne_of_gt hk, ite_false, zero_mul] using h

end FreeProbability

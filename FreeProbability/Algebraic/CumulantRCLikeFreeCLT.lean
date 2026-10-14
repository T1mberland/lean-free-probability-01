import FreeProbability.Algebraic.CumulantFreeCLT
import FreeProbability.Algebraic.CumulantLowOrder
import Mathlib.Analysis.RCLike.Basic

/-!
# The algebraic free central limit theorem over real or complex scalars

The inverse-square-root normalization is a real scalar embedded into `𝕜`.
For any `RCLike` scalar field, centered iid free sums have all power moments
converging to the explicit noncrossing-pairing sequence with the actual second
moment. Source algebras may vary with size. No spectral or norm limit is claimed.
-/

namespace FreeProbability

open Filter Topology

private theorem real_normalization_coefficient_tendsto {k : ℕ} (hk : 2 ≤ k) :
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

variable {𝕜 E : Type*} [RCLike 𝕜] [Ring E] [Algebra 𝕜 E]

/-- The all-order cumulant limit over real or complex scalars. -/
theorem freeCLT_cumulants_rclike {D : ℕ → Type*} [∀ N, Ring (D N)] [∀ N, Algebra 𝕜 (D N)]
    (φN : ∀ N, ProbabilitySpace 𝕜 (D N)) (B : ∀ N, Fin N → Subalgebra 𝕜 (D N))
    (aN : ∀ N, Fin N → D N) (ψ : ProbabilitySpace 𝕜 E) (b : E)
    (hfree : ∀ N, FreelyIndependent (φN N) (B N))
    (hmem : ∀ N i, aN N i ∈ B N i)
    (hmarg : ∀ N i k, (φN N).expectation (aN N i ^ k) = ψ.expectation (b ^ k))
    (hcenter : ψ.expectation b = 0) (k : ℕ) :
    Tendsto (fun N => cumulant (φN N)
      (List.replicate k (((Real.sqrt (N : ℝ))⁻¹ : 𝕜) • ∑ i, aN N i))) atTop
      (𝓝 (if k = 2 then ψ.expectation (b ^ 2) else 0)) := by
  have hexact (N : ℕ) := (hfree N).cumulant_replicate_scaled_sum
    (aN N) (hmem N) ψ b (hmarg N) ((Real.sqrt (N : ℝ))⁻¹ : 𝕜) k
  simp only [Fintype.card_fin] at hexact
  by_cases hk0 : k = 0
  · subst k
    simp only [List.replicate_zero, cumulant, freeCumulant_nil, Nat.reduceEqDiff, ite_false]
    exact tendsto_const_nhds
  by_cases hk1 : k = 1
  · subst k
    have hzero (N : ℕ) := (hfree N).cumulant_one_scaled_sum
      (aN N) (hmem N) ψ b (hmarg N) hcenter ((Real.sqrt (N : ℝ))⁻¹ : 𝕜)
    simpa only [List.replicate_succ, List.replicate_zero, Nat.reduceEqDiff, ite_false, hzero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : 𝕜)) atTop (𝓝 0))
  have hk : 2 ≤ k := by omega
  have hreal := real_normalization_coefficient_tendsto hk
  have hcast : Tendsto (fun N : ℕ => (((Real.sqrt (N : ℝ))⁻¹ ^ k * (N : ℝ) : ℝ) : 𝕜)) atTop
      (𝓝 ((if k = 2 then 1 else 0 : ℝ) : 𝕜)) :=
    RCLike.continuous_ofReal.continuousAt.tendsto.comp hreal
  have h := hcast.mul_const (cumulant ψ (List.replicate k b))
  have hfun (N : ℕ) : (((Real.sqrt (N : ℝ))⁻¹ ^ k * (N : ℝ) : ℝ) : 𝕜) *
      cumulant ψ (List.replicate k b) =
      cumulant (φN N) (List.replicate k (((Real.sqrt (N : ℝ))⁻¹ : 𝕜) • ∑ i, aN N i)) := by
    rw [hexact N]
    simp only [map_mul, map_pow, map_natCast, map_inv₀, mul_assoc]
  have hlim : ((if k = 2 then 1 else 0 : ℝ) : 𝕜) * cumulant ψ (List.replicate k b) =
      if k = 2 then ψ.expectation (b ^ 2) else 0 := by
    by_cases hk2 : k = 2
    · subst k
      simp [cumulant_pair_self_of_centered ψ b hcenter]
    · simp [hk2]
  rw [hlim] at h
  exact h.congr hfun

/-- The explicit pairing-moment free central limit theorem over real or complex scalars. -/
theorem freeCLT_pairingMoments_rclike {D : ℕ → Type*} [∀ N, Ring (D N)] [∀ N, Algebra 𝕜 (D N)]
    (φN : ∀ N, ProbabilitySpace 𝕜 (D N)) (B : ∀ N, Fin N → Subalgebra 𝕜 (D N))
    (aN : ∀ N, Fin N → D N) (ψ : ProbabilitySpace 𝕜 E) (b : E)
    (hfree : ∀ N, FreelyIndependent (φN N) (B N))
    (hmem : ∀ N i, aN N i ∈ B N i)
    (hmarg : ∀ N i k, (φN N).expectation (aN N i ^ k) = ψ.expectation (b ^ k))
    (hcenter : ψ.expectation b = 0) (k : ℕ) :
    Tendsto (fun N => (φN N).expectation
      ((((Real.sqrt (N : ℝ))⁻¹ : 𝕜) • ∑ i, aN N i) ^ k)) atTop
      (𝓝 ((Fintype.card (NoncrossingPairing k) : 𝕜) * ψ.expectation (b ^ 2) ^ (k / 2))) := by
  classical
  let M (N : ℕ) (w : List Unit) := (φN N).expectation
    ((((Real.sqrt (N : ℝ))⁻¹ : 𝕜) • ∑ i, aN N i) ^ w.length)
  have hM0 (N : ℕ) : M N [] = 1 := by simp [M]
  have hK (w : List Unit) : Tendsto (fun N => freeCumulant (M N) w) atTop
      (𝓝 (pairingCumulantShape (ψ.expectation (b ^ 2)) w)) := by
    simpa only [M, freeCumulant_powerMoments, pairingCumulantShape] using
      freeCLT_cumulants_rclike φN B aN ψ b hfree hmem hmarg hcenter w.length
  let w : List Unit := List.replicate k ()
  have hsum : Tendsto (fun N => ∑ p : NoncrossingPartition w.length,
      partitionContribution (freeCumulant (M N)) w p) atTop
      (𝓝 (∑ p : NoncrossingPartition w.length,
        partitionContribution (pairingCumulantShape (ψ.expectation (b ^ 2))) w p)) := by
    apply tendsto_finsetSum
    intro p _
    unfold partitionContribution
    apply tendsto_finsetProd
    intro s _
    exact hK (blockWord w s.val)
  simpa only [← moment_cumulant_formula_all _ (hM0 _) w,
    sum_partitionContribution_pairingCumulantShape, M, w, List.length_replicate] using hsum

end FreeProbability

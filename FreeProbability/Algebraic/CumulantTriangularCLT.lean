import FreeProbability.Algebraic.CumulantTriangularEstimates

/-!
# The quantitative non-iid free central limit theorem

Centered free triangular arrays have the semicircular cumulant and pairing
moment limits if their averaged second moments converge and each fixed marginal
cumulant of order greater than two is bounded uniformly over all rows and entries.
Source algebras may vary. Identical distribution is not assumed.
-/

namespace FreeProbability

open Filter Topology

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The full semicircular cumulant limit of centered, non-iid free triangular arrays. -/
theorem freeCLT_triangular_cumulants {D : ℕ → Type*} [∀ N, Ring (D N)]
    [∀ N, Algebra 𝕜 (D N)] (φ : ∀ N, ProbabilitySpace 𝕜 (D N))
    (B : ∀ N, Fin N → Subalgebra 𝕜 (D N)) (a : ∀ N, Fin N → D N) (σ : 𝕜)
    (hfree : ∀ N, FreelyIndependent (φ N) (B N)) (hmem : ∀ N i, a N i ∈ B N i)
    (hcenter : ∀ N i, (φ N).expectation (a N i) = 0)
    (hvariance : Tendsto (fun N : ℕ => (N : 𝕜)⁻¹ * ∑ i, (φ N).expectation (a N i ^ 2))
      atTop (𝓝 σ))
    (hbound : ∀ k, 2 < k → ∃ C : ℝ,
      ∀ N i, ‖cumulant (φ N) (List.replicate k (a N i))‖ ≤ C) (k : ℕ) :
    Tendsto (fun N => cumulant (φ N)
      (List.replicate k (((Real.sqrt (N : ℝ))⁻¹ : 𝕜) • ∑ i, a N i))) atTop
      (𝓝 (if k = 2 then σ else 0)) := by
  classical
  have hexact (N : ℕ) : cumulant (φ N)
      (List.replicate k (((Real.sqrt (N : ℝ))⁻¹ : 𝕜) • ∑ i, a N i)) =
      (((Real.sqrt (N : ℝ))⁻¹ : 𝕜) ^ k) * ∑ i, cumulant (φ N) (List.replicate k (a N i)) := by
    rw [cumulant_replicate_smul, (hfree N).cumulant_replicate_sum (a N) (hmem N)]
  by_cases hk0 : k = 0
  · subst k
    simp only [List.replicate_zero, cumulant, freeCumulant_nil, Nat.reduceEqDiff, ite_false]
    exact tendsto_const_nhds
  by_cases hk1 : k = 1
  · subst k
    have hz (N : ℕ) : cumulant (φ N)
        (List.replicate 1 (((Real.sqrt (N : ℝ))⁻¹ : 𝕜) • ∑ i, a N i)) = 0 := by
      rw [hexact]
      simp [cumulant_singleton, hcenter]
    simpa only [hz, Nat.reduceEqDiff, ite_false] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : 𝕜)) atTop (𝓝 0))
  by_cases hk2 : k = 2
  · subst k
    have he (N : ℕ) : cumulant (φ N)
        (List.replicate 2 (((Real.sqrt (N : ℝ))⁻¹ : 𝕜) • ∑ i, a N i)) =
        (N : 𝕜)⁻¹ * ∑ i, (φ N).expectation (a N i ^ 2) := by
      rw [hexact]
      have hs : ((Real.sqrt (N : ℝ) : 𝕜)) ^ 2 = (N : 𝕜) := by
        rw [← map_pow, Real.sq_sqrt (Nat.cast_nonneg _), map_natCast]
      rw [inv_pow, hs]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      simpa only [List.replicate_succ, List.replicate_zero] using
        cumulant_pair_self_of_centered (φ N) (a N i) (hcenter N i)
    simpa only [ite_true] using hvariance.congr (fun N => (he N).symm)
  have hk : 2 < k := by omega
  obtain ⟨C, hC⟩ := hbound k hk
  simpa only [hk2, ite_false] using
    freeCLT_triangular_higher_cumulants φ B a hfree hmem k hk C hC

/-- All normalized non-iid free triangular-array power moments converge to the
explicit pairing moment sequence under the quantified cumulant bound assumptions. -/
theorem freeCLT_triangular_pairingMoments {D : ℕ → Type*} [∀ N, Ring (D N)]
    [∀ N, Algebra 𝕜 (D N)] (φ : ∀ N, ProbabilitySpace 𝕜 (D N))
    (B : ∀ N, Fin N → Subalgebra 𝕜 (D N)) (a : ∀ N, Fin N → D N) (σ : 𝕜)
    (hfree : ∀ N, FreelyIndependent (φ N) (B N)) (hmem : ∀ N i, a N i ∈ B N i)
    (hcenter : ∀ N i, (φ N).expectation (a N i) = 0)
    (hvariance : Tendsto (fun N : ℕ => (N : 𝕜)⁻¹ * ∑ i, (φ N).expectation (a N i ^ 2))
      atTop (𝓝 σ))
    (hbound : ∀ k, 2 < k → ∃ C : ℝ,
      ∀ N i, ‖cumulant (φ N) (List.replicate k (a N i))‖ ≤ C) (k : ℕ) :
    Tendsto (fun N => (φ N).expectation
      ((((Real.sqrt (N : ℝ))⁻¹ : 𝕜) • ∑ i, a N i) ^ k)) atTop
      (𝓝 ((Fintype.card (NoncrossingPairing k) : 𝕜) * σ ^ (k / 2))) := by
  classical
  let M (N : ℕ) (w : List Unit) := (φ N).expectation
    ((((Real.sqrt (N : ℝ))⁻¹ : 𝕜) • ∑ i, a N i) ^ w.length)
  have hM0 (N : ℕ) : M N [] = 1 := by simp [M]
  have hK (w : List Unit) : Tendsto (fun N => freeCumulant (M N) w) atTop
      (𝓝 (pairingCumulantShape σ w)) := by
    simpa only [M, freeCumulant_powerMoments, pairingCumulantShape] using
      freeCLT_triangular_cumulants φ B a σ hfree hmem hcenter hvariance hbound w.length
  let w : List Unit := List.replicate k ()
  have hsum : Tendsto (fun N => ∑ p : NoncrossingPartition w.length,
      partitionContribution (freeCumulant (M N)) w p) atTop
      (𝓝 (∑ p : NoncrossingPartition w.length,
        partitionContribution (pairingCumulantShape σ) w p)) := by
    apply tendsto_finsetSum
    intro p _
    unfold partitionContribution
    apply tendsto_finsetProd
    intro s _
    exact hK (blockWord w s.val)
  simpa only [← moment_cumulant_formula_all _ (hM0 _) w,
    sum_partitionContribution_pairingCumulantShape, M, w, List.length_replicate] using hsum

end FreeProbability

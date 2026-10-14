import FreeProbability.RandomMatrix.OrthogonalInvariantSpanning

/-! # Genuine stable-dimension orthogonal Weingarten entry integration -/

noncomputable section
open scoped Classical RealInnerProductSpace
namespace FreeProbability.Orthogonal
open Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The actual Haar projection is obtained by the TRUE inverse Gram matrix
of all ordinary pairing tensors, in stable dimension. -/
theorem tensorPowerAverage_eq_pairingGram_inverse {r : ℕ} (hr : r ≤ Fintype.card n)
    (v : EuclideanSpace ℝ (Fin (2 * r) → n)) :
    (tensorPowerRepresentation (n := n) (2 * r)).averageCLM v =
      ∑ p : OrdinaryPairing r,
        (∑ q : OrdinaryPairing r, (ordinaryPairingGram n r)⁻¹ p q *
          ⟪ordinaryPairingTensor (n := n) q, v⟫) • ordinaryPairingTensor p := by
  let ρ := tensorPowerRepresentation (n := n) (2 * r)
  have hav : ρ.average v ∈ ρ.fixedVectors := fun g => ρ.action_average g v
  have hspan := invariantTensor_mem_span_pairings hr (ρ.average v) hav
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hspan
  let d : OrdinaryPairing r → ℝ := fun p => ⟪ordinaryPairingTensor (n := n) p, v⟫
  have hG : ordinaryPairingGram n r *ᵥ c = d := by
    funext p
    have he := ρ.inner_average_of_fixed (pairingTensor_mem_fixedVectors p.out) v
    rw [← hc] at he
    simp only [inner_sum, inner_smul_right] at he
    simpa only [ordinaryPairingGram_eq_gram, Matrix.mulVec, dotProduct,
      Matrix.gram_apply, mul_comm, ordinaryPairingTensor, d] using he
  have hcinv : c = (ordinaryPairingGram n r)⁻¹ *ᵥ d := by
    have he := congrArg (fun z => (ordinaryPairingGram n r)⁻¹ *ᵥ z) hG
    rw [mulVec_mulVec, (ordinaryPairingGram_inverse r hr).2, one_mulVec] at he
    exact he
  change ρ.average v = _
  rw [← hc, hcinv]
  rfl

private theorem inner_tensorBasisVector (r : ℕ) (q : OrdinaryPairing r) (j : Fin (2 * r) → n) :
    ⟪ordinaryPairingTensor (n := n) q, tensorBasisVector (2 * r) j⟫ = (ordinaryPairingTensor q) j := by
  change ⟪ordinaryPairingTensor (n := n) q, EuclideanSpace.single j (1 : ℝ)⟫ = _
  rw [EuclideanSpace.inner_single_right]
  simp

/-- The FULL genuine even Haar entry moment is the ordinary pairing sum with
the actual inverse Gram matrix. No pairing integration formula is assumed. -/
theorem entryMoment_eq_weingarten_sum {r : ℕ} (hr : r ≤ Fintype.card n)
    (i j : Fin (2 * r) → n) :
    entryMoment i j = ∑ p : OrdinaryPairing r, ∑ q : OrdinaryPairing r,
      (ordinaryPairingTensor (n := n) p) i * (ordinaryPairingGram n r)⁻¹ p q *
        (ordinaryPairingTensor q) j := by
  rw [← tensorPowerAverage_basis_coefficient (2 * r) i j]
  have he := congrArg (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (2 * r) → n => ℝ) i)
    (tensorPowerAverage_eq_pairingGram_inverse hr (tensorBasisVector (2 * r) j))
  simp only [map_sum, map_smul, inner_tensorBasisVector] at he
  change ((tensorPowerRepresentation (n := n) (2 * r)).averageCLM (tensorBasisVector (2 * r) j)) i =
    ∑ p : OrdinaryPairing r, (∑ q : OrdinaryPairing r,
      (ordinaryPairingGram n r)⁻¹ p q * (ordinaryPairingTensor q) j) * (ordinaryPairingTensor p) i at he
  calc
    _ = _ := he
    _ = _ := by
      change (∑ p : OrdinaryPairing r, (∑ q : OrdinaryPairing r,
        (ordinaryPairingGram n r)⁻¹ p q * (ordinaryPairingTensor q) j) *
          (ordinaryPairingTensor p) i) = _
      simp_rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      ring
/-- The literal product of ordinary paired Kronecker deltas. -/
def ordinaryPairingDelta {r : ℕ} (p : OrdinaryPairing r) (i : Fin (2 * r) → n) : ℝ :=
  ∏ a : Fin r, if i (p.out.symm (a, 0)) = i (p.out.symm (a, 1)) then 1 else 0

/-- The same genuine integration theorem in explicit Kronecker-delta form. -/
theorem entryMoment_eq_weingarten_delta_sum {r : ℕ} (hr : r ≤ Fintype.card n)
    (i j : Fin (2 * r) → n) :
    entryMoment i j = ∑ p : OrdinaryPairing r, ∑ q : OrdinaryPairing r,
      ordinaryPairingDelta p i * (ordinaryPairingGram n r)⁻¹ p q * ordinaryPairingDelta q j := by
  simpa only [ordinaryPairingTensor, pairingTensor_coefficient, ordinaryPairingDelta] using
    entryMoment_eq_weingarten_sum hr i j
end FreeProbability.Orthogonal

import FreeProbability.RandomMatrix.OrthogonalInvariantRotation

/-! # Genuine zero-coefficient step from normalized fresh-color splitting -/

noncomputable section
open scoped Classical
namespace FreeProbability.Orthogonal
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] in
private theorem colorSplitTuple_all_false {k : ℕ} (i : Fin k → n) (c d : n) :
    colorSplitTuple i c d (fun _ => false) = i := by
  funext a
  by_cases h : i a = c <;> simp [colorSplitTuple, h]

omit [Fintype n] in
private theorem colorSplitTuple_all_true {k : ℕ} (i : Fin k → n) (c d : n)
    (hfresh : ∀ a, i a ≠ d) :
    colorSplitTuple i c d (fun _ => true) = fun a => Equiv.swap c d (i a) := by
  funext a
  by_cases h : i a = c
  · simp [colorSplitTuple, h]
  · simp [colorSplitTuple, h, Equiv.swap_apply_def, hfresh a]

/-- The exact normalized rotation weight is strictly contractive for every
block of size at least four. -/
theorem twice_planeMixerWeight_pow_lt_one (m : ℕ) (hm : 4 ≤ m) :
    2 * ((Real.sqrt 2)⁻¹ : ℝ) ^ m < 1 := by
  let q : ℝ := (Real.sqrt 2)⁻¹
  have hq0 : 0 ≤ q := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hq2 : q ^ 2 = 1 / 2 := by
    simp only [q, inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hq1 : q ≤ 1 := by nlinarith
  have hq4 : q ^ 4 = 1 / 4 := by
    rw [show 4 = 2 * 2 by decide, pow_mul, hq2]
    norm_num
  have hle := pow_le_pow_of_le_one hq0 hq1 hm
  change 2 * q ^ m < 1
  rw [hq4] at hle
  nlinarith

/-- If every proper fresh-color split vanishes, genuine fixedness forces the
original coefficient to vanish. No scalar recurrence is assumed. -/
theorem invariantTensor_coefficient_eq_zero_of_proper_splits {k : ℕ}
    (v : EuclideanSpace ℝ (Fin k → n))
    (hv : v ∈ (tensorPowerRepresentation (n := n) k).fixedVectors)
    (i : Fin k → n) (c d : n) (hcd : c ≠ d) (hfresh : ∀ a, i a ≠ d)
    (hm : 4 ≤ (Finset.univ.filter (fun a => i a = c)).card)
    (hproper : ∀ γ : ColorSites i c → Bool,
      γ ≠ (fun _ => false) → γ ≠ (fun _ => true) → v (colorSplitTuple i c d γ) = 0) :
    v i = 0 := by
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < (Finset.univ.filter (fun a => i a = c)).card by omega)
  let a0 : ColorSites i c := ⟨a, (Finset.mem_filter.mp ha).2⟩
  have hft : (fun _ : ColorSites i c => false) ≠ (fun _ => true) := by
    intro he
    have h := congrFun he a0
    simp only [Bool.false_eq_true] at h
  have hfalse : v (colorSplitTuple i c d (fun _ => false)) = v i := by
    rw [colorSplitTuple_all_false]
  have htrue : v (colorSplitTuple i c d (fun _ => true)) = v i := by
    rw [colorSplitTuple_all_true i c d hfresh]
    exact invariantTensor_permutation v hv i (Equiv.swap c d)
  have hsplit (γ : ColorSites i c → Bool) :
      v (colorSplitTuple i c d γ) =
        (if γ = (fun _ => false) then v i else 0) + (if γ = (fun _ => true) then v i else 0) := by
    by_cases hf : γ = (fun _ => false)
    · subst γ
      simp only [hfalse, ite_true, hft, ite_false, add_zero]
    · by_cases ht : γ = (fun _ => true)
      · subst γ
        simp only [htrue, hf, ite_false, ite_true, zero_add]
      · simp only [hproper γ hf ht, hf, ht, ite_false, zero_add]
  have hsum : (∑ γ : ColorSites i c → Bool, v (colorSplitTuple i c d γ)) = 2 * v i := by
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring
  have he := invariantTensor_fresh_color_split v hv i c d hcd hfresh
  rw [hsum] at he
  have hlt := twice_planeMixerWeight_pow_lt_one _ hm
  have hn : 1 - 2 * ((Real.sqrt 2)⁻¹ : ℝ) ^ (Finset.univ.filter (fun a => i a = c)).card ≠ 0 := by linarith
  have hz : (1 - 2 * ((Real.sqrt 2)⁻¹ : ℝ) ^ (Finset.univ.filter (fun a => i a = c)).card) * v i = 0 := by
    nlinarith [he]
  exact (mul_eq_zero.mp hz).resolve_left hn
end FreeProbability.Orthogonal

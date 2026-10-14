import FreeProbability.RandomMatrix.OrthogonalPlaneMixing

/-! # Exact fourth moments of a row of a real Haar orthogonal matrix -/

namespace FreeProbability.Orthogonal

open Matrix MeasureTheory

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem integrable_row_powers (r c d : n) (k l : ℕ) :
    Integrable (fun U : Group n => (U r c) ^ k * (U r d) ^ l) (haar n) := by
  have hc : Continuous (fun U : Group n => U r c) :=
    (continuous_apply c).comp ((continuous_apply r).comp continuous_subtype_val)
  have hd : Continuous (fun U : Group n => U r d) :=
    (continuous_apply d).comp ((continuous_apply r).comp continuous_subtype_val)
  exact ((hc.pow k).mul (hd.pow l)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem integral_entry_pow_eq (r c d : n) (k : ℕ) :
    (∫ U : Group n, (U r c) ^ k ∂haar n) = ∫ U : Group n, (U r d) ^ k ∂haar n := by
  have h := integral_mul_right_eq_self (μ := haar n)
    (fun U : Group n => (U r c) ^ k) (permutation (Equiv.swap c d))
  simp only [mul_permutation_apply, Equiv.symm_swap, Equiv.swap_apply_left] at h
  exact h.symm

theorem integral_entry_pow_mul_eq_zero (r c d : n) (hcd : c ≠ d) (k l : ℕ) (hl : Odd l) :
    (∫ U : Group n, (U r c) ^ k * (U r d) ^ l ∂haar n) = 0 := by
  have h := integral_mul_right_eq_self (μ := haar n)
    (fun U : Group n => (U r c) ^ k * (U r d) ^ l) (coordinateReflection d)
  have he : ∀ U : Group n,
      ((U * coordinateReflection d) r c) ^ k * ((U * coordinateReflection d) r d) ^ l =
        -((U r c) ^ k * (U r d) ^ l) := by
    intro U
    simp [mul_coordinateReflection_apply, hcd, hl.neg_pow]
  simp_rw [he] at h
  rw [integral_neg] at h
  linarith

theorem integral_row_sum_pow_four (r c d : n) (hcd : c ≠ d) :
    (∫ U : Group n, (U r c + U r d) ^ 4 ∂haar n) =
      (∫ U : Group n, (U r c) ^ 4 ∂haar n) +
        6 * (∫ U : Group n, (U r c) ^ 2 * (U r d) ^ 2 ∂haar n) +
          (∫ U : Group n, (U r d) ^ 4 ∂haar n) := by
  have h1 : Integrable (fun U : Group n => (U r c) ^ 4) (haar n) := by
    simpa using integrable_row_powers r c d 4 0
  have h2 := (integrable_row_powers r c d 3 1).const_mul 4
  have h3 := (integrable_row_powers r c d 2 2).const_mul 6
  have h4 := (integrable_row_powers r c d 1 3).const_mul 4
  have h5 : Integrable (fun U : Group n => (U r d) ^ 4) (haar n) := by
    simpa using integrable_row_powers r c d 0 4
  have he (U : Group n) : (U r c + U r d) ^ 4 =
      (U r c) ^ 4 + 4 * ((U r c) ^ 3 * (U r d) ^ 1) +
        6 * ((U r c) ^ 2 * (U r d) ^ 2) +
          4 * ((U r c) ^ 1 * (U r d) ^ 3) + (U r d) ^ 4 := by ring
  simp_rw [he]
  have ha1 := integral_add h1 h2
  have ha2 := integral_add (h1.add h2) h3
  have ha3 := integral_add ((h1.add h2).add h3) h4
  have ha4 := integral_add (((h1.add h2).add h3).add h4) h5
  simp only [Pi.add_apply] at ha1 ha2 ha3 ha4
  rw [ha4, ha3, ha2, ha1, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_entry_pow_mul_eq_zero r c d hcd 3 1 (by decide),
    integral_entry_pow_mul_eq_zero r c d hcd 1 3 (by decide)]
  ring

/-- A plane rotation gives the factor three between diagonal and mixed fourth moments. -/
theorem integral_entry_four_eq_three_mixed (r c d : n) (hcd : c ≠ d) :
    (∫ U : Group n, (U r c) ^ 4 ∂haar n) =
      3 * (∫ U : Group n, (U r c) ^ 2 * (U r d) ^ 2 ∂haar n) := by
  have hs : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hq : ((Real.sqrt 2)⁻¹) ^ 4 = (1 / 4 : ℝ) := by
    calc
      _ = (((Real.sqrt 2)⁻¹) ^ 2) ^ 2 := by ring
      _ = _ := by rw [inv_pow, hs]; norm_num
  have h := integral_mul_right_eq_self (μ := haar n)
    (fun U : Group n => (U r c) ^ 4) (planeMixer c d hcd)
  simp_rw [mul_planeMixer_apply, mul_pow] at h
  rw [integral_const_mul, hq, integral_row_sum_pow_four r c d hcd,
    integral_entry_pow_eq r d c 4] at h
  linarith

theorem integral_mixed_sq_eq (r c d e : n) (hcd : c ≠ d) (hce : c ≠ e) :
    (∫ U : Group n, (U r c) ^ 2 * (U r d) ^ 2 ∂haar n) =
      ∫ U : Group n, (U r c) ^ 2 * (U r e) ^ 2 ∂haar n := by
  have h := integral_mul_right_eq_self (μ := haar n)
    (fun U : Group n => (U r c) ^ 2 * (U r d) ^ 2) (permutation (Equiv.swap d e))
  simp only [mul_permutation_apply, Equiv.symm_swap, Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne hcd hce] at h
  exact h.symm

theorem integral_entry_sq_mul_sq (r c d : n) (hcd : c ≠ d) :
    (∫ U : Group n, (U r c) ^ 2 * (U r d) ^ 2 ∂haar n) =
      1 / ((Fintype.card n : ℝ) * ((Fintype.card n : ℝ) + 2)) := by
  let b := ∫ U : Group n, (U r c) ^ 2 * (U r d) ^ 2 ∂haar n
  have hs : (∑ j, ∫ U : Group n, (U r c) ^ 2 * (U r j) ^ 2 ∂haar n) =
      (Fintype.card n : ℝ)⁻¹ := by
    rw [← integral_finsetSum Finset.univ (fun j _ => integrable_row_powers r c j 2 2)]
    have he (U : Group n) : (∑ j, (U r c) ^ 2 * (U r j) ^ 2) = (U r c) ^ 2 := by
      rw [← Finset.mul_sum, sum_row_sq, mul_one]
    simp_rw [he]
    exact integral_entry_sq r c
  have hj (j : n) : (∫ U : Group n, (U r c) ^ 2 * (U r j) ^ 2 ∂haar n) =
      if j = c then 3 * b else b := by
    by_cases he : j = c
    · subst j
      rw [ite_eq_left rfl]
      have hp (U : Group n) : (U r c) ^ 2 * (U r c) ^ 2 = (U r c) ^ 4 := by ring
      simp_rw [hp]
      exact integral_entry_four_eq_three_mixed r c d hcd
    · rw [ite_eq_right he]
      exact integral_mixed_sq_eq r c j d (Ne.symm he) hcd
  simp_rw [hj] at hs
  have hN : 1 ≤ Fintype.card n := by
    let _ : Nonempty n := ⟨r⟩
    exact Fintype.card_pos_iff.mpr inferInstance
  have hsum : (∑ j : n, if j = c then 3 * b else b) = ((Fintype.card n : ℝ) + 2) * b := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ c), ite_eq_left rfl]
    have herase : (∑ j ∈ Finset.univ.erase c, if j = c then 3 * b else b) =
        ((Fintype.card n : ℝ) - 1) * b := by
      calc
        _ = ∑ _j ∈ Finset.univ.erase c, b := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [ite_eq_right (Finset.ne_of_mem_erase hj)]
        _ = _ := by simp [Finset.card_erase_of_mem, nsmul_eq_mul, Nat.cast_sub hN]
    rw [herase]
    ring
  rw [hsum] at hs
  have hNr : (0 : ℝ) < Fintype.card n := by exact_mod_cast hN
  have h0 : (Fintype.card n : ℝ) ≠ 0 := hNr.ne'
  have h2 : (Fintype.card n : ℝ) + 2 ≠ 0 := by linarith
  change b = _
  apply (eq_div_iff (mul_ne_zero h0 h2)).mpr
  have he := congrArg ((Fintype.card n : ℝ) * ·) hs
  simp only [mul_inv_cancel₀ h0] at he
  nlinarith

/-- The diagonal fourth moment, including the one-dimensional orthogonal group. -/
theorem integral_entry_pow_four (r c : n) :
    (∫ U : Group n, (U r c) ^ 4 ∂haar n) =
      3 / ((Fintype.card n : ℝ) * ((Fintype.card n : ℝ) + 2)) := by
  by_cases hnt : Nontrivial n
  · let _ := hnt
    obtain ⟨d, hd⟩ := exists_ne c
    rw [integral_entry_four_eq_three_mixed r c d hd.symm,
      integral_entry_sq_mul_sq r c d hd.symm]
    ring
  · have hs : Subsingleton n := not_nontrivial_iff_subsingleton.mp hnt
    let _ := hs
    have hcard : Fintype.card n = 1 := Fintype.card_eq_one_of_forall_eq
      (fun j => Subsingleton.elim j c)
    have hp (U : Group n) : (U r c) ^ 4 = 1 := by
      have hsq : (U r c) ^ 2 = 1 := by
        simpa only [Fintype.sum_subsingleton _ c] using sum_row_sq U r
      calc
        _ = ((U r c) ^ 2) ^ 2 := by ring
        _ = 1 := by rw [hsq]; norm_num
    simp_rw [hp]
    norm_num [hcard]

theorem integral_entry_sq_mul_sq_all (r c d : n) :
    (∫ U : Group n, (U r c) ^ 2 * (U r d) ^ 2 ∂haar n) =
      (if c = d then 3 else 1) / ((Fintype.card n : ℝ) * ((Fintype.card n : ℝ) + 2)) := by
  by_cases hcd : c = d
  · subst d
    have he (U : Group n) : (U r c) ^ 2 * (U r c) ^ 2 = (U r c) ^ 4 := by ring
    simp_rw [he]
    simpa using integral_entry_pow_four r c
  · simpa [hcd] using integral_entry_sq_mul_sq r c d hcd

theorem integral_row_four_zero_of_singleton (r c d e f : n)
    (hcd : c ≠ d) (hce : c ≠ e) (hcf : c ≠ f) :
    (∫ U : Group n, U r c * U r d * U r e * U r f ∂haar n) = 0 := by
  have h := integral_mul_right_eq_self (μ := haar n)
    (fun U : Group n => U r c * U r d * U r e * U r f) (coordinateReflection c)
  have he (U : Group n) :
      (U * coordinateReflection c) r c * (U * coordinateReflection c) r d *
        (U * coordinateReflection c) r e * (U * coordinateReflection c) r f =
          -(U r c * U r d * U r e * U r f) := by
    simp [mul_coordinateReflection_apply, (Ne.symm hcd), (Ne.symm hce), (Ne.symm hcf)]
  simp_rw [he] at h
  rw [integral_neg] at h
  linarith

theorem integrable_row_product_four (r c d e f : n) :
    Integrable (fun U : Group n => U r c * U r d * U r e * U r f) (haar n) := by
  have hc (j : n) : Continuous (fun U : Group n => U r j) :=
    (continuous_apply j).comp ((continuous_apply r).comp continuous_subtype_val)
  exact ((((hc c).mul (hc d)).mul (hc e)).mul (hc f)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The full fourth-moment tensor of a Haar row, in Kronecker-pairing form. -/
theorem integral_row_product_four (r c d e f : n) :
    (∫ U : Group n, U r c * U r d * U r e * U r f ∂haar n) =
      ((if c = d ∧ e = f then 1 else 0) + (if c = e ∧ d = f then 1 else 0) +
        (if c = f ∧ d = e then 1 else 0)) /
          ((Fintype.card n : ℝ) * ((Fintype.card n : ℝ) + 2)) := by
  have hswap (c d e f : n) :
      (∫ U : Group n, U r c * U r d * U r e * U r f ∂haar n) =
        ∫ U : Group n, U r e * U r c * U r d * U r f ∂haar n := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun U => by ring)
  have hpair (c d : n) :
      (∫ U : Group n, U r c * U r c * U r d * U r d ∂haar n) =
        (if c = d then 3 else 1) /
          ((Fintype.card n : ℝ) * ((Fintype.card n : ℝ) + 2)) := by
    simpa only [pow_two, mul_assoc] using integral_entry_sq_mul_sq_all r c d
  by_cases hcd : c = d
  · subst d
    by_cases hef : e = f
    · subst f
      rw [hpair]
      by_cases hce : c = e <;> norm_num [hce]
    · have hz : (∫ U : Group n, U r c * U r c * U r e * U r f ∂haar n) = 0 := by
        by_cases hec : e = c
        · subst e
          have hs := integral_row_four_zero_of_singleton r f c c c
            (Ne.symm hef) (Ne.symm hef) (Ne.symm hef)
          have he : (∫ U : Group n, U r c * U r c * U r c * U r f ∂haar n) =
              ∫ U : Group n, U r f * U r c * U r c * U r c ∂haar n := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall (fun U => by ring)
          exact he.trans hs
        · rw [hswap]
          exact integral_row_four_zero_of_singleton r e c c f hec hec hef
      rw [hz]
      by_cases hce : c = e <;> simp [hef, hce]
  · by_cases hce : c = e
    · subst e
      by_cases hdf : d = f
      · subst f
        have he : (∫ U : Group n, U r c * U r d * U r c * U r d ∂haar n) =
            ∫ U : Group n, U r c * U r c * U r d * U r d ∂haar n := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun U => by ring)
        rw [he, hpair]
        simp [hcd, (Ne.symm hcd)]
      · have he : (∫ U : Group n, U r c * U r d * U r c * U r f ∂haar n) =
            ∫ U : Group n, U r d * U r c * U r c * U r f ∂haar n := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun U => by ring)
        rw [he, integral_row_four_zero_of_singleton r d c c f (Ne.symm hcd) (Ne.symm hcd) hdf]
        simp [hcd, (Ne.symm hcd), hdf]
    · by_cases hcf : c = f
      · subst f
        by_cases hde : d = e
        · subst e
          have he : (∫ U : Group n, U r c * U r d * U r d * U r c ∂haar n) =
              ∫ U : Group n, U r c * U r c * U r d * U r d ∂haar n := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall (fun U => by ring)
          rw [he, hpair]
          simp [hcd, (Ne.symm hcd)]
        · have he : (∫ U : Group n, U r c * U r d * U r e * U r c ∂haar n) =
              ∫ U : Group n, U r d * U r c * U r e * U r c ∂haar n := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall (fun U => by ring)
          rw [he, integral_row_four_zero_of_singleton r d c e c (Ne.symm hcd) hde (Ne.symm hcd)]
          simp [hcd, hce, hde]
      · rw [integral_row_four_zero_of_singleton r c d e f hcd hce hcf]
        simp [hcd, hce, hcf]

end FreeProbability.Orthogonal

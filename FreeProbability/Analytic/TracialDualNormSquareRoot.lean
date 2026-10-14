import FreeProbability.Analytic.TracialDualNormRegularization

/-! # Actual reciprocal-square-root factors in the positive CFC -/

namespace FreeProbability

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

noncomputable def tracialRegularizedRoot (a : A) (ε : ℝ) : A :=
  cfc (fun x : ℝ => Real.sqrt (x + ε)) a

noncomputable def tracialRegularizedRootInverse (a : A) (ε : ℝ) : A :=
  cfc (fun x : ℝ => (Real.sqrt (x + ε))⁻¹) a

omit [PartialOrder A] [StarOrderedRing A] in
private theorem rootShift_continuousOn (a : A) (ε : ℝ) :
    ContinuousOn (fun x : ℝ => Real.sqrt (x + ε)) (spectrum ℝ a) :=
  Real.continuous_sqrt.comp_continuousOn (continuousOn_id.add continuousOn_const)

private theorem rootInverseShift_continuousOn (a : A) (ha : 0 ≤ a)
    (ε : ℝ) (hε : 0 < ε) :
    ContinuousOn (fun x : ℝ => (Real.sqrt (x + ε))⁻¹) (spectrum ℝ a) := by
  apply (rootShift_continuousOn a ε).inv₀
  intro x hx
  exact ne_of_gt (Real.sqrt_pos.mpr
    (add_pos_of_nonneg_of_pos (spectrum_nonneg_of_nonneg ha hx) hε))

theorem tracialRegularizedRoot_nonneg (a : A) (ε : ℝ) :
    0 ≤ tracialRegularizedRoot a ε :=
  cfc_nonneg (fun x _ => Real.sqrt_nonneg (x + ε))

theorem tracialRegularizedRootInverse_nonneg (a : A) (ε : ℝ) :
    0 ≤ tracialRegularizedRootInverse a ε :=
  cfc_nonneg (fun x _ => inv_nonneg.mpr (Real.sqrt_nonneg (x + ε)))

theorem tracialRegularizedRoot_square (a : A) (ha : 0 ≤ a)
    (ε : ℝ) (hε : 0 < ε) :
    tracialRegularizedRoot a ε * tracialRegularizedRoot a ε =
      a + algebraMap ℝ A ε := by
  have hs : cfc (fun x : ℝ => x + ε) a = a + algebraMap ℝ A ε := by
    rw [cfc_add a (fun x : ℝ => x) (fun _ : ℝ => ε) continuousOn_id continuousOn_const,
      cfc_id' ℝ a (IsSelfAdjoint.of_nonneg ha),
      cfc_const ε a (IsSelfAdjoint.of_nonneg ha)]
  rw [tracialRegularizedRoot, ← cfc_mul _ _ a
    (rootShift_continuousOn a ε) (rootShift_continuousOn a ε), ← hs]
  apply cfc_congr
  intro x hx
  exact Real.mul_self_sqrt (le_of_lt
    (add_pos_of_nonneg_of_pos (spectrum_nonneg_of_nonneg ha hx) hε))

theorem tracialRegularizedRootInverse_mul_root (a : A) (ha : 0 ≤ a)
    (ε : ℝ) (hε : 0 < ε) :
    tracialRegularizedRootInverse a ε * tracialRegularizedRoot a ε = 1 := by
  rw [tracialRegularizedRootInverse, tracialRegularizedRoot, ← cfc_mul _ _ a
    (rootInverseShift_continuousOn a ha ε hε) (rootShift_continuousOn a ε),
    ← cfc_const_one ℝ a (IsSelfAdjoint.of_nonneg ha)]
  apply cfc_congr
  intro x hx
  exact inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr
    (add_pos_of_nonneg_of_pos (spectrum_nonneg_of_nonneg ha hx) hε)))

theorem tracialRegularizedRootInverse_square_bound (a : A) (ha : 0 ≤ a)
    (ε : ℝ) (hε : 0 < ε) :
    tracialRegularizedRootInverse a ε * (a * a) * tracialRegularizedRootInverse a ε ≤ a := by
  have hc := rootInverseShift_continuousOn a ha ε hε
  have ha' := IsSelfAdjoint.of_nonneg ha
  have he : tracialRegularizedRootInverse a ε * (a * a) * tracialRegularizedRootInverse a ε =
      cfc (fun x : ℝ => (Real.sqrt (x + ε))⁻¹ * (x * x) * (Real.sqrt (x + ε))⁻¹) a := by
    have hi : cfc (fun x : ℝ => x * x) a = a * a := by
      rw [cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) a continuousOn_id continuousOn_id,
        cfc_id' ℝ a ha']
    rw [tracialRegularizedRootInverse, ← hi,
      ← cfc_mul (fun x : ℝ => (Real.sqrt (x + ε))⁻¹) (fun x : ℝ => x * x) a hc
        (continuousOn_id.mul continuousOn_id),
      ← cfc_mul (fun x : ℝ => (Real.sqrt (x + ε))⁻¹ * (x * x))
        (fun x : ℝ => (Real.sqrt (x + ε))⁻¹) a
        (hc.mul (continuousOn_id.mul continuousOn_id)) hc]
  rw [he]
  conv_rhs => rw [← cfc_id' ℝ a ha']
  apply (cfc_le_iff _ _ a
    (hc.mul (continuousOn_id.mul continuousOn_id) |>.mul hc) continuousOn_id ha').mpr
  intro x hx
  have hx0 := spectrum_nonneg_of_nonneg ha hx
  have hxε : 0 < x + ε := add_pos_of_nonneg_of_pos hx0 hε
  change (Real.sqrt (x + ε))⁻¹ * (x * x) * (Real.sqrt (x + ε))⁻¹ ≤ x
  have heq : (Real.sqrt (x + ε))⁻¹ * (x * x) * (Real.sqrt (x + ε))⁻¹ =
      (x * x) / (x + ε) := by
    conv_rhs => rw [← Real.mul_self_sqrt hxε.le]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heq, div_le_iff₀ hxε]
  nlinarith [mul_nonneg hx0 hε.le]

end FreeProbability

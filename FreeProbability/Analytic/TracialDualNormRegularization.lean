import FreeProbability.Analytic.TracialDualNorm

/-! # Positive CFC regularization for the trace dual norm -/

namespace FreeProbability

open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The actual real CFC reciprocal of a shifted positive operator. -/
noncomputable def tracialRegularizedInverse (a : A) (ε : ℝ) : A :=
  cfc (fun x : ℝ => (x + ε)⁻¹) a

private theorem inverseShift_continuousOn (a : A) (ha : 0 ≤ a)
    (ε : ℝ) (hε : 0 < ε) :
    ContinuousOn (fun x : ℝ => (x + ε)⁻¹) (spectrum ℝ a) := by
  apply ContinuousOn.inv₀ (continuousOn_id.add continuousOn_const)
  intro x hx
  exact ne_of_gt (add_pos_of_nonneg_of_pos (spectrum_nonneg_of_nonneg ha hx) hε)

theorem tracialRegularizedInverse_nonneg (a : A) (ha : 0 ≤ a)
    (ε : ℝ) (hε : 0 < ε) : 0 ≤ tracialRegularizedInverse a ε := by
  unfold tracialRegularizedInverse
  exact cfc_nonneg (fun x hx => inv_nonneg.mpr
    (le_of_lt (add_pos_of_nonneg_of_pos (spectrum_nonneg_of_nonneg ha hx) hε)))

theorem tracialRegularizedInverse_mul_shift (a : A) (ha : 0 ≤ a)
    (ε : ℝ) (hε : 0 < ε) :
    tracialRegularizedInverse a ε * (a + algebraMap ℝ A ε) = 1 := by
  have hs : cfc (fun x : ℝ => x + ε) a = a + algebraMap ℝ A ε := by
    rw [cfc_add a (fun x : ℝ => x) (fun _ : ℝ => ε) continuousOn_id continuousOn_const,
      cfc_id' ℝ a (IsSelfAdjoint.of_nonneg ha),
      cfc_const ε a (IsSelfAdjoint.of_nonneg ha)]
  rw [tracialRegularizedInverse, ← hs,
    ← cfc_mul (fun x : ℝ => (x + ε)⁻¹) (fun x : ℝ => x + ε) a (inverseShift_continuousOn a ha ε hε)
      (continuousOn_id.add continuousOn_const), ← cfc_const_one ℝ a (IsSelfAdjoint.of_nonneg ha)]
  apply cfc_congr
  intro x hx
  exact inv_mul_cancel₀ (ne_of_gt
    (add_pos_of_nonneg_of_pos (spectrum_nonneg_of_nonneg ha hx) hε))

theorem tracialRegularizedInverse_square_bound (a : A) (ha : 0 ≤ a)
    (ε : ℝ) (hε : 0 < ε) :
    tracialRegularizedInverse a ε * (a * a) * tracialRegularizedInverse a ε ≤ 1 := by
  have hc := inverseShift_continuousOn a ha ε hε
  have ha' := IsSelfAdjoint.of_nonneg ha
  have he : tracialRegularizedInverse a ε * (a * a) * tracialRegularizedInverse a ε =
      cfc (fun x : ℝ => (x + ε)⁻¹ * (x * x) * (x + ε)⁻¹) a := by
    have hi : cfc (fun x : ℝ => x * x) a = a * a := by
      rw [cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) a continuousOn_id continuousOn_id,
        cfc_id' ℝ a ha']
    rw [tracialRegularizedInverse, ← hi,
      ← cfc_mul (fun x : ℝ => (x + ε)⁻¹) (fun x : ℝ => x * x) a hc
        (continuousOn_id.mul continuousOn_id),
      ← cfc_mul (fun x : ℝ => (x + ε)⁻¹ * (x * x)) (fun x : ℝ => (x + ε)⁻¹)
        a (hc.mul (continuousOn_id.mul continuousOn_id)) hc]
  rw [he, ← cfc_const_one ℝ a (IsSelfAdjoint.of_nonneg ha)]
  apply (cfc_le_iff _ _ a
    (hc.mul (continuousOn_id.mul continuousOn_id) |>.mul hc)
    continuousOn_const ha').mpr
  intro x hx
  have hx0 := spectrum_nonneg_of_nonneg ha hx
  have hxε : 0 < x + ε := add_pos_of_nonneg_of_pos hx0 hε
  have hq : 0 ≤ x / (x + ε) := div_nonneg hx0 hxε.le
  have hq1 : x / (x + ε) ≤ 1 := (div_le_one hxε).mpr (by linarith)
  have hh : x / (x + ε) * (x / (x + ε)) ≤ 1 :=
    (mul_le_mul hq1 hq1 hq zero_le_one).trans_eq (one_mul 1)
  change (x + ε)⁻¹ * (x * x) * (x + ε)⁻¹ ≤ 1
  convert hh using 1
  simp only [div_eq_mul_inv]
  ring

theorem tracialRegularizedInverse_lower_bound (a : A) (ha : 0 ≤ a)
    (ε : ℝ) (hε : 0 < ε) :
    a - algebraMap ℝ A ε ≤ tracialRegularizedInverse a ε * (a * a) := by
  have hc := inverseShift_continuousOn a ha ε hε
  have ha' := IsSelfAdjoint.of_nonneg ha
  have he : tracialRegularizedInverse a ε * (a * a) =
      cfc (fun x : ℝ => (x + ε)⁻¹ * (x * x)) a := by
    have hi : cfc (fun x : ℝ => x * x) a = a * a := by
      rw [cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) a continuousOn_id continuousOn_id,
        cfc_id' ℝ a ha']
    rw [tracialRegularizedInverse, ← hi,
      ← cfc_mul (fun x : ℝ => (x + ε)⁻¹) (fun x : ℝ => x * x) a hc
        (continuousOn_id.mul continuousOn_id)]
  have hs : cfc (fun x : ℝ => x - ε) a = a - algebraMap ℝ A ε := by
    rw [cfc_sub (fun x : ℝ => x) (fun _ : ℝ => ε) a continuousOn_id continuousOn_const,
      cfc_id' ℝ a ha', cfc_const ε a ha']
  rw [← hs, he]
  apply (cfc_le_iff _ _ a (continuousOn_id.sub continuousOn_const)
    (hc.mul (continuousOn_id.mul continuousOn_id)) ha').mpr
  intro x hx
  have hxε : 0 < x + ε := add_pos_of_nonneg_of_pos
    (spectrum_nonneg_of_nonneg ha hx) hε
  change x - ε ≤ (x + ε)⁻¹ * (x * x)
  rw [← div_eq_inv_mul, le_div_iff₀ hxε]
  nlinarith [sq_nonneg ε]

end FreeProbability

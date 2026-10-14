import FreeProbability.OperatorValued.PositiveOperatorEnergy
import Mathlib.Topology.Order.MonotoneConvergence

/-! # Actual quadratic coefficients and increment bounds for monotone operator nets -/
noncomputable section
open scoped InnerProductSpace
open Filter
namespace FreeProbability
variable {J H : Type*} [Preorder J] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem positiveOperatorQuadratic_monotone (T : J → (H →L[ℂ] H)) (hT : Monotone T) (x : H) :
    Monotone (fun j => (inner ℂ x (T j x)).re) := by
  intro i j hij
  have hp : 0 ≤ T j - T i := sub_nonneg.mpr (hT hij)
  have h := (ContinuousLinearMap.nonneg_iff_isPositive.mp hp).re_inner_nonneg_right x
  simpa only [sub_apply, inner_sub_right, map_sub,
    RCLike.re_eq_complex_re, sub_nonneg] using h

omit [Preorder J] [CompleteSpace H] in
theorem positiveOperatorQuadratic_bddAbove (T : J → (H →L[ℂ] H)) (M : ℝ)
    (hM : ∀ j, ‖T j‖ ≤ M) (x : H) :
    BddAbove (Set.range (fun j => (inner ℂ x (T j x)).re)) := by
  refine ⟨‖x‖ * (M * ‖x‖), ?_⟩
  rintro _ ⟨j, rfl⟩
  calc
    _ ≤ ‖inner ℂ x (T j x)‖ := Complex.re_le_norm _
    _ ≤ ‖x‖ * ‖T j x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (M * ‖x‖) := mul_le_mul_of_nonneg_left
      ((T j).le_opNorm x |>.trans (mul_le_mul_of_nonneg_right (hM j) (norm_nonneg x)))
      (norm_nonneg x)

omit [CompleteSpace H] in
theorem positiveOperatorQuadratic_tendsto (T : J → (H →L[ℂ] H)) (hT : Monotone T)
    (M : ℝ) (hM : ∀ j, ‖T j‖ ≤ M) (x : H) :
    Tendsto (fun j => (inner ℂ x (T j x)).re) atTop
      (nhds (⨆ j, (inner ℂ x (T j x)).re)) :=
  tendsto_atTop_ciSup (positiveOperatorQuadratic_monotone T hT x)
    (positiveOperatorQuadratic_bddAbove T M hM x)

theorem positiveOperator_increment_energy_le (T : J → (H →L[ℂ] H)) (hT : Monotone T)
    (M : ℝ) (hM : ∀ j, ‖T j‖ ≤ M) (x : H) {i j : J} (hij : i ≤ j) :
    ‖T j x - T i x‖ ^ 2 ≤ (2 * M) *
      ((inner ℂ x (T j x)).re - (inner ℂ x (T i x)).re) := by
  have hp : 0 ≤ T j - T i := sub_nonneg.mpr (hT hij)
  have hn : ‖T j - T i‖ ≤ 2 * M :=
    (norm_sub_le _ _).trans (by linarith [hM i, hM j])
  have hq : 0 ≤ (inner ℂ x ((T j - T i) x)).re := by
    simpa only [RCLike.re_eq_complex_re] using
      (ContinuousLinearMap.nonneg_iff_isPositive.mp hp).re_inner_nonneg_right x
  have he := positiveOperator_energy_le (T j - T i) hp x
  have hb := he.trans (mul_le_mul_of_nonneg_right hn hq)
  simpa only [sub_apply, inner_sub_right, Complex.sub_re] using hb
end FreeProbability

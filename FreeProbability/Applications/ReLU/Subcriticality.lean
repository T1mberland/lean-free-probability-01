import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The algebraic edge calculation for the ReLU exceptional channel

This proves the finite geometric-sum calculation and the strict deficit below
one at every depth at least three. Identifying this expression as the physical
secular edge limit needs the S-transform and random cavity limits. The rational
physical-interval monotonicity is proved separately in `EdgeCalculus`.
-/

namespace FreeProbability.ReLU

theorem geometric_defect_sum (r : ℝ) (m : ℕ) :
    ∑ k ∈ Finset.range m, (1 - r) * r ^ k = 1 - r ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring

/-- The finite geometric expression obtained at the critical parameter. -/
noncomputable def edgeSecularExpression (L : ℕ) : ℝ :=
  (1 / (L : ℝ)) * (∑ k ∈ Finset.range (L - 1), (1 - 1 / (L : ℝ)) ^ k) +
    (2 / (L : ℝ)) * (1 - 1 / (L : ℝ)) ^ (L - 1)

/-- Exact simplification of the finite geometric expression. -/
theorem edgeSecularExpression_eq (L : ℕ) :
    edgeSecularExpression L =
      1 - (1 - 2 / (L : ℝ)) * (1 - 1 / (L : ℝ)) ^ (L - 1) := by
  let q : ℝ := 1 - 1 / (L : ℝ)
  have hq : 1 / (L : ℝ) = 1 - q := by dsimp [q]; ring
  have hs : (1 / (L : ℝ)) * (∑ k ∈ Finset.range (L - 1), q ^ k) = 1 - q ^ (L - 1) := by
    rw [hq, Finset.mul_sum]
    exact geometric_defect_sum q (L - 1)
  change (1 / (L : ℝ)) * (∑ k ∈ Finset.range (L - 1), q ^ k) +
    (2 / (L : ℝ)) * q ^ (L - 1) = 1 - (1 - 2 / (L : ℝ)) * q ^ (L - 1)
  rw [hs]
  ring

/-- The explicit subcritical margin is strictly positive for every depth `L ≥ 3`. -/
theorem edge_deficit_pos (L : ℕ) (hL : 3 ≤ L) :
    0 < (1 - 2 / (L : ℝ)) * (1 - 1 / (L : ℝ)) ^ (L - 1) := by
  have hLR : (3 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hpos : (0 : ℝ) < L := by linarith
  have htwo : 0 < 1 - 2 / (L : ℝ) := by
    apply sub_pos.mpr
    exact (div_lt_one hpos).mpr (by linarith)
  have hone : 0 < 1 - 1 / (L : ℝ) := by
    apply sub_pos.mpr
    exact (div_lt_one hpos).mpr (by linarith)
  exact mul_pos htwo (pow_pos hone _)

theorem edgeSecularExpression_lt_one (L : ℕ) (hL : 3 ≤ L) : edgeSecularExpression L < 1 := by
  rw [edgeSecularExpression_eq]
  linarith [edge_deficit_pos L hL]

@[simp] theorem edgeSecularExpression_three : edgeSecularExpression 3 = (23 / 27 : ℝ) := by
  norm_num [edgeSecularExpression_eq]

@[simp] theorem edgeSecularExpression_four : edgeSecularExpression 4 = (101 / 128 : ℝ) := by
  norm_num [edgeSecularExpression_eq]

end FreeProbability.ReLU

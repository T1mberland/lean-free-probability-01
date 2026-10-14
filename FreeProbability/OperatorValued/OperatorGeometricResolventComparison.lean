import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Genuine geometric inverse comparison from retained vector powers

This generic estimate is conditional on retained powers. Actual finite-depth
Fock propagation and pencil compression are separate obligations.
-/
noncomputable section
open scoped Classical Ring
namespace FreeProbability
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Power application bounds include the zero Banach space, without a norm-one identity assumption. -/
theorem operator_pow_apply_norm_le (A : E →L[ℂ] E) (q : ℝ) (hq : 0 ≤ q)
    (hA : ‖A‖ ≤ q) (k : ℕ) (x : E) : ‖(A ^ k) x‖ ≤ q ^ k * ‖x‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp]
    calc
      ‖A ((A ^ k) x)‖ ≤ ‖A‖ * ‖(A ^ k) x‖ := A.le_opNorm _
      _ ≤ q * (q ^ k * ‖x‖) := mul_le_mul hA ih (norm_nonneg _) hq
      _ = q ^ (k + 1) * ‖x‖ := by rw [pow_succ]; ring

/-- If two contractions retain the first L+1 powers of a vector, their actual geometric inverses differ only by an explicitly bounded tail. -/
theorem geometricInverse_apply_comparison (A B : E →L[ℂ] E) (q : ℝ)
    (hq : 0 ≤ q) (hq1 : q < 1) (hA : ‖A‖ ≤ q) (hB : ‖B‖ ≤ q)
    (L : ℕ) (x : E) (hp : ∀ k ≤ L, (A ^ k) x = (B ^ k) x) :
    ‖(1 - A)⁻¹ʳ x - (1 - B)⁻¹ʳ x‖ ≤
      2 * q ^ (L + 1) / (1 - q) * ‖x‖ := by
  have ha := (ContinuousLinearMap.apply ℂ E x).hasSum
    (hasSum_geom_series_inverse A (hA.trans_lt hq1))
  have hb := (ContinuousLinearMap.apply ℂ E x).hasSum
    (hasSum_geom_series_inverse B (hB.trans_lt hq1))
  simp only [ContinuousLinearMap.apply_apply] at ha hb
  have hs := ha.sub hb
  have ht := (hasSum_nat_add_iff' (L + 1)).mpr hs
  have hz : ∑ k ∈ Finset.range (L + 1), ((A ^ k) x - (B ^ k) x) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [hp k (by simpa using Finset.mem_range.mp hk), sub_self]
  rw [hz, sub_zero] at ht
  have hg : HasSum (fun k : ℕ => 2 * q ^ (k + (L + 1)) * ‖x‖)
      (2 * q ^ (L + 1) / (1 - q) * ‖x‖) := by
    have hh : ‖q‖ < 1 := by simpa only [Real.norm_of_nonneg hq] using hq1
    simpa only [pow_add, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (hasSum_geometric_of_norm_lt_one hh).mul_left (2 * q ^ (L + 1) * ‖x‖)
  apply ht.norm_le_of_bounded hg
  intro k
  calc
    ‖(A ^ (k + (L + 1))) x - (B ^ (k + (L + 1))) x‖ ≤
        ‖(A ^ (k + (L + 1))) x‖ + ‖(B ^ (k + (L + 1))) x‖ := norm_sub_le _ _
    _ ≤ q ^ (k + (L + 1)) * ‖x‖ + q ^ (k + (L + 1)) * ‖x‖ :=
      add_le_add (operator_pow_apply_norm_le A q hq hA _ x)
        (operator_pow_apply_norm_le B q hq hB _ x)
    _ = _ := by ring

end FreeProbability

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Banach

/-! # Exact powers retained by a sandwich compression -/
noncomputable section
namespace FreeProbability
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Retention along a single orbit suffices; the projection need not be the identity elsewhere. -/
theorem operator_sandwich_pow_apply_eq (Q A : E →L[ℂ] E) (L : ℕ) (x : E)
    (hQ : ∀ k ≤ L, Q ((A ^ k) x) = (A ^ k) x) :
    ∀ k ≤ L, ((Q * A * Q) ^ k) x = (A ^ k) x := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hk' : k ≤ L := (Nat.le_succ k).trans hk
    rw [pow_succ', mul_apply_eq_comp, ih hk']
    rw [mul_apply_eq_comp, mul_apply_eq_comp, hQ k hk']
    simpa only [pow_succ', mul_apply_eq_comp] using hQ (k + 1) hk

end FreeProbability

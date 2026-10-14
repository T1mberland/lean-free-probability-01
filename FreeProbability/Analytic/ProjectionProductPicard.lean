import FreeProbability.Analytic.ProjectionProductMomentEquation
import Mathlib.Topology.Order.MonotoneConvergence

/-! # Genuine scalar Picard majorants for the half-projection moment equation -/

noncomputable section
open scoped Topology
namespace FreeProbability

/-- Picard iterates of the normalized half-projection implicit equation. -/
def halfProjectionPicard (L : ℕ) (t : ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => (t / (2 : ℝ) ^ L) * (1 + halfProjectionPicard L t k) ^ L

theorem halfProjectionPicard_nonneg (L : ℕ) (t : ℝ) (ht : 0 ≤ t) (k : ℕ) :
    0 ≤ halfProjectionPicard L t k := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact mul_nonneg (div_nonneg ht (by positivity)) (pow_nonneg (by linarith) L)

/-- The actual scalar Picard iterates increase. -/
theorem halfProjectionPicard_monotone (L : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    Monotone (halfProjectionPicard L t) := by
  apply monotone_nat_of_le_succ
  intro k
  induction k with
  | zero => exact halfProjectionPicard_nonneg L t ht 1
  | succ k ih =>
    apply mul_le_mul_of_nonneg_left
    · exact pow_le_pow_left₀ (by linarith [halfProjectionPicard_nonneg L t ht k])
        (by linarith) L
    · exact div_nonneg ht (by positivity)

/-- Every nonnegative scalar supersolution bounds all Picard iterates. This
is a quantitative majorant, not an assumed bound on the actual law. -/
theorem halfProjectionPicard_le_supersolution (L : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (r : ℝ) (hr : 0 ≤ r) (hsuper : (t / (2 : ℝ) ^ L) * (1 + r) ^ L ≤ r) (k : ℕ) :
    halfProjectionPicard L t k ≤ r := by
  induction k with
  | zero => exact hr
  | succ k ih =>
    exact (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith [halfProjectionPicard_nonneg L t ht k])
        (by linarith) L) (div_nonneg ht (by positivity))).trans hsuper

/-- A nonnegative supersolution yields genuine convergence of the scalar
Picard sequence to its supremum. -/
theorem halfProjectionPicard_tendsto (L : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (r : ℝ) (hr : 0 ≤ r) (hsuper : (t / (2 : ℝ) ^ L) * (1 + r) ^ L ≤ r) :
    Filter.Tendsto (halfProjectionPicard L t) Filter.atTop
      (𝓝 (⨆ k, halfProjectionPicard L t k)) := by
  apply tendsto_atTop_ciSup (halfProjectionPicard_monotone L t ht)
  exact ⟨r, by rintro x ⟨k, rfl⟩; exact halfProjectionPicard_le_supersolution L t ht r hr hsuper k⟩

/-- The limit of the genuinely bounded Picard iterates solves the normalized
implicit equation. Its relation to the actual moment series is a separate step. -/
theorem halfProjectionPicard_limit_fixedPoint (L : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (r : ℝ) (hr : 0 ≤ r) (hsuper : (t / (2 : ℝ) ^ L) * (1 + r) ^ L ≤ r) :
    (⨆ k, halfProjectionPicard L t k) =
      (t / (2 : ℝ) ^ L) * (1 + ⨆ k, halfProjectionPicard L t k) ^ L := by
  have hlim := halfProjectionPicard_tendsto L t ht r hr hsuper
  have hshift := hlim.comp (Filter.tendsto_add_atTop_nat 1)
  have hc : Continuous (fun x : ℝ => (t / (2 : ℝ) ^ L) * (1 + x) ^ L) := by fun_prop
  have hmap := (hc.tendsto (⨆ k, halfProjectionPicard L t k)).comp hlim
  exact tendsto_nhds_unique hshift (by simpa only [Function.comp_def, halfProjectionPicard] using hmap)
/-- The genuine Picard limit remains below every nonnegative supersolution,
so in particular it is the least nonnegative fixed point when one exists. -/
theorem halfProjectionPicard_limit_le_supersolution (L : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (r : ℝ) (hr : 0 ≤ r) (hsuper : (t / (2 : ℝ) ^ L) * (1 + r) ^ L ≤ r) :
    (⨆ k, halfProjectionPicard L t k) ≤ r :=
  ciSup_le (fun k => halfProjectionPicard_le_supersolution L t ht r hr hsuper k)

/-- The genuine Picard limit is nonnegative whenever its iterates have a
nonnegative scalar supersolution. -/
theorem halfProjectionPicard_limit_nonneg (L : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (r : ℝ) (hr : 0 ≤ r) (hsuper : (t / (2 : ℝ) ^ L) * (1 + r) ^ L ≤ r) :
    0 ≤ (⨆ k, halfProjectionPicard L t k) := by
  have hb : BddAbove (Set.range (halfProjectionPicard L t)) :=
    ⟨r, by rintro x ⟨k, rfl⟩; exact halfProjectionPicard_le_supersolution L t ht r hr hsuper k⟩
  exact (halfProjectionPicard_nonneg L t ht 0).trans (le_ciSup hb 0)
end FreeProbability

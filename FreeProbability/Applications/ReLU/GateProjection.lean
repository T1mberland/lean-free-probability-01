import FreeProbability.RandomMatrix.OrthogonalGateLaw
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real

/-! # ReLU diagonal gates and their actual matrix ranks -/

namespace FreeProbability.ReLU

open Matrix
open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable def gateProjection (v : n → ℝ) : Matrix n n ℝ :=
  diagonal (fun i => if 0 < v i then 1 else 0)

theorem gateProjection_idempotent (v : n → ℝ) : gateProjection v * gateProjection v = gateProjection v := by
  classical
  rw [gateProjection, diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases hi : 0 < v i <;> simp [hi]

omit [Fintype n] in
theorem gateProjection_symmetric (v : n → ℝ) : (gateProjection v)ᵀ = gateProjection v := by
  rw [gateProjection, diagonal_transpose]

omit [Fintype n] in
theorem gateProjection_posSemidef (v : n → ℝ) : (gateProjection v).PosSemidef := by
  classical
  rw [gateProjection, posSemidef_diagonal_iff]
  intro i
  by_cases hi : 0 < v i <;> simp [hi]

/-- The binomial gate count is the actual matrix rank of the ReLU diagonal gate. -/
theorem gateProjection_rank (v : n → ℝ) : (gateProjection v).rank = Orthogonal.gateRank v := by
  classical
  rw [gateProjection, Matrix.rank_diagonal]
  have he (i : n) : (if 0 < v i then (1 : ℝ) else 0) ≠ 0 ↔ 0 < v i := by
    by_cases hi : 0 < v i <;> simp [hi]
  calc
    _ = Fintype.card {i : n // 0 < v i} := Fintype.card_congr (Equiv.subtypeEquivRight he)
    _ = (Orthogonal.positiveSet v).ncard := Set.fintypeCard_eq_ncard _
    _ = Orthogonal.gateRank v := rfl

theorem gateProjection_trace (v : n → ℝ) : (gateProjection v).trace = (Orthogonal.gateRank v : ℝ) := by
  classical
  have hc : Orthogonal.gateRank v = Fintype.card {i : n // 0 < v i} :=
    (Set.fintypeCard_eq_ncard (Orthogonal.positiveSet v)).symm
  rw [hc]
  simp [gateProjection, Matrix.trace_diagonal, Fintype.card_subtype]

theorem gateProjection_norm_le_one (v : n → ℝ) : ‖gateProjection v‖ ≤ 1 := by
  classical
  rw [gateProjection, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro i
  by_cases hi : 0 < v i <;> simp [hi]

/-- The explicit normalized one-layer gated weight matrix. -/
noncomputable def gatedWeight (v : n → ℝ) (U : Orthogonal.Group n) : Matrix n n ℝ :=
  gateProjection v * (U : Matrix n n ℝ)

theorem gatedWeight_norm_le_one [Nonempty n] (v : n → ℝ) (U : Orthogonal.Group n) :
    ‖gatedWeight v U‖ ≤ 1 := by
  unfold gatedWeight
  calc
    _ ≤ ‖gateProjection v‖ * ‖(U : Matrix n n ℝ)‖ := norm_mul_le _ _
    _ = ‖gateProjection v‖ := by rw [CStarRing.norm_coe_unitary U, mul_one]
    _ ≤ 1 := gateProjection_norm_le_one v

theorem gatedWeight_product_norm_le_one [Nonempty n]
    (layers : List ((n → ℝ) × Orthogonal.Group n)) :
    ‖(layers.map (fun p => gatedWeight p.1 p.2)).prod‖ ≤ 1 := by
  induction layers with
  | nil => simp
  | cons p layers ih =>
    simp only [List.map_cons, List.prod_cons]
    calc
      _ ≤ ‖gatedWeight p.1 p.2‖ * ‖(layers.map (fun q => gatedWeight q.1 q.2)).prod‖ := norm_mul_le _ _
      _ ≤ 1 * 1 := mul_le_mul (gatedWeight_norm_le_one _ _) ih (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num

theorem gateProjection_haar_rank_hasLaw (x : n → ℝ) (hx : x ≠ 0) :
    ProbabilityTheory.HasLaw
      (fun U : Orthogonal.Group n => (gateProjection ((U : Matrix n n ℝ) *ᵥ x)).rank)
      (ProbabilityTheory.binomial (Fintype.card n) Orthogonal.halfProbability) (Orthogonal.haar n) := by
  simpa only [gateProjection_rank] using Orthogonal.gateRank_haar_hasLaw x hx

end FreeProbability.ReLU

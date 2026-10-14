import FreeProbability.RandomMatrix.OrthogonalSecondMoment
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # An exact orthogonal change of two coordinates -/

namespace FreeProbability.Orthogonal

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The symmetric plane mixer fixing every coordinate outside `c,d`. -/
def planeMixerMatrix (c d : n) (q : ℝ) : Matrix n n ℝ := fun i =>
  if i = c then q • Pi.single c 1 + q • Pi.single d 1
  else if i = d then q • Pi.single c 1 - q • Pi.single d 1
  else Pi.single i 1

theorem planeMixerMatrix_mem (c d : n) (hcd : c ≠ d) (q : ℝ) (hq : 2 * q ^ 2 = 1) :
    planeMixerMatrix c d q ∈ Matrix.orthogonalGroup n ℝ := by
  apply (Matrix.mem_orthogonalGroup_iff n ℝ).mpr
  ext i j
  change planeMixerMatrix c d q i ⬝ᵥ planeMixerMatrix c d q j = _
  have hqq : q * q = (1 / 2 : ℝ) := by nlinarith [hq]
  clear hq
  by_cases hic : i = c <;> by_cases hid : i = d <;>
    by_cases hjc : j = c <;> by_cases hjd : j = d <;>
    simp_all [planeMixerMatrix, dotProduct_add, dotProduct_sub, dotProduct_smul,
      single_dotProduct, Pi.single_apply, Matrix.one_apply, smul_eq_mul, eq_comm] <;> nlinarith

noncomputable def planeMixer (c d : n) (hcd : c ≠ d) : Group n :=
  ⟨planeMixerMatrix c d ((Real.sqrt 2)⁻¹), planeMixerMatrix_mem c d hcd _ (by
    have hs : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    rw [inv_pow, hs]
    norm_num)⟩

omit [Fintype n] in
theorem planeMixerMatrix_column (c d : n) (hcd : c ≠ d) (q : ℝ) :
    (fun i => planeMixerMatrix c d q i c) = q • Pi.single c 1 + q • Pi.single d 1 := by
  funext i
  by_cases hic : i = c <;> by_cases hid : i = d <;>
    simp_all [planeMixerMatrix]

theorem mul_planeMixer_apply (c d : n) (hcd : c ≠ d) (U : Group n) (r : n) :
    (U * planeMixer c d hcd) r c = (Real.sqrt 2)⁻¹ * (U r c + U r d) := by
  change (U : Matrix n n ℝ) r ⬝ᵥ (fun i => planeMixerMatrix c d ((Real.sqrt 2)⁻¹) i c) = _
  rw [planeMixerMatrix_column c d hcd]
  simp [dotProduct_add, dotProduct_smul, dotProduct_single]
  ring

end FreeProbability.Orthogonal

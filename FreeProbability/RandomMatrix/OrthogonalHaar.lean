/-
SPDX-License-Identifier: Apache-2.0
The compact-Haar normalization and uniqueness proofs are adapted from
T1mberland/lean-weingarten, Weingarten/Haar.lean, revision e3a09fdfaeeab526388990a52b9911dd8e955ab2.
See LICENSES/Apache-2.0.txt.
-/
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic.Linarith

/-!
# Normalized Haar probability on real orthogonal matrices

Compactness follows from closedness and the entrywise unit bound. Haar measure
is normalized on the whole group, with uniqueness, left/right invariance, and
inversion invariance. Matrix entry monomials are continuous and integrable.

The unitary counterpart in `lean-weingarten` motivated this module; orthogonal
moment integration and the one-column conditional law remain separate theorems.
-/

namespace FreeProbability.Orthogonal

open Matrix MeasureTheory

abbrev Group (n : Type*) [Fintype n] [DecidableEq n] := Matrix.orthogonalGroup n ℝ

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem sum_row_sq (U : Group n) (i : n) : ∑ j, (U i j) ^ 2 = 1 := by
  have he := (Matrix.mem_orthogonalGroup_iff n ℝ).mp U.property
  have h := congrFun (congrFun he i) i
  simpa [Matrix.mul_apply, Matrix.transpose_apply, pow_two] using h

theorem norm_entry_le_one (U : Group n) (i j : n) : ‖U i j‖ ≤ 1 := by
  have hs : (U i j) ^ 2 ≤ 1 := by
    rw [← sum_row_sq U i]
    exact Finset.single_le_sum (fun k _ => sq_nonneg _) (Finset.mem_univ j)
  rw [Real.norm_eq_abs]
  exact (sq_le_one_iff_abs_le_one (U i j)).mp hs

instance : CompactSpace (Group n) := by
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall (0 : ℝ) 1).matrix.of_isClosed_subset isClosed_unitary
  intro U hU i j
  simpa only [Metric.mem_closedBall, dist_zero_right] using norm_entry_le_one ⟨U, hU⟩ i j

instance : SecondCountableTopology (Group n) := by
  let _ : SecondCountableTopology (Matrix n n ℝ) :=
    inferInstanceAs (SecondCountableTopology (n → n → ℝ))
  exact TopologicalSpace.Subtype.secondCountableTopology
    (Matrix.orthogonalGroup n ℝ : Set (Matrix n n ℝ))

instance : MeasurableSpace (Group n) := borel _
instance : BorelSpace (Group n) := ⟨rfl⟩

/-- Haar probability measure on the full real orthogonal group. -/
noncomputable def haar (n : Type*) [Fintype n] [DecidableEq n] : Measure (Group n) :=
  Measure.haarMeasure ⊤

instance : Measure.IsHaarMeasure (haar n) := by unfold haar; infer_instance

instance : IsProbabilityMeasure (haar n) where
  measure_univ := Measure.haarMeasure_self

/-- Left-invariant probability measures agree with the normalized Haar measure. -/
theorem eq_haar (μ : Measure (Group n)) [IsProbabilityMeasure μ]
    [μ.IsMulLeftInvariant] : μ = haar n := by
  have h := Measure.isMulInvariant_eq_smul_of_compactSpace μ (haar n)
  have hm := congrArg (fun ν : Measure (Group n) => ν Set.univ) h
  have hc : Measure.haarScalarFactor μ (haar n) = 1 := by
    simpa only [Measure.smul_apply, measure_univ, ENNReal.smul_def, smul_eq_mul, mul_one,
      ENNReal.coe_eq_one] using hm.symm
  simpa [hc] using h

instance : (haar n).IsMulRightInvariant where
  map_mul_right_eq_self U := by
    exact eq_haar _

instance : (haar n).IsInvInvariant where
  inv_eq_self := by
    let _ : IsProbabilityMeasure (haar n).inv :=
      ⟨by rw [Measure.inv_apply]; simp⟩
    exact eq_haar _

/-- A genuine product of real matrix entries, not a combinatorial integration formula. -/
def entryMonomial {k : ℕ} (i j : Fin k → n) (U : Group n) : ℝ := ∏ a, U (i a) (j a)

theorem continuous_entryMonomial {k : ℕ} (i j : Fin k → n) :
    Continuous (entryMonomial i j) := by
  unfold entryMonomial
  apply continuous_finsetProd
  intro a _
  exact (continuous_apply (j a)).comp ((continuous_apply (i a)).comp continuous_subtype_val)

theorem integrable_entryMonomial {k : ℕ} (i j : Fin k → n) :
    Integrable (entryMonomial i j) (haar n) :=
  (continuous_entryMonomial i j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Entry moments are actual Bochner integrals against Haar probability. -/
noncomputable def entryMoment {k : ℕ} (i j : Fin k → n) : ℝ :=
  ∫ U, entryMonomial i j U ∂haar n

@[simp] theorem entryMoment_zero (i j : Fin 0 → n) : entryMoment i j = 1 := by
  simp [entryMoment, entryMonomial]

theorem entryMonomial_neg {k : ℕ} (i j : Fin k → n) (U : Group n) :
    entryMonomial i j (-U) = (-1 : ℝ) ^ k * entryMonomial i j U := by
  change (∏ a : Fin k, -(U (i a) (j a))) = _
  simp [entryMonomial, Finset.prod_neg]

/-- Odd-degree real orthogonal Haar entry moments vanish in every dimension. -/
theorem entryMoment_eq_zero_of_odd {k : ℕ} (i j : Fin k → n) (hk : Odd k) :
    entryMoment i j = 0 := by
  have heq := integral_mul_left_eq_self (μ := haar n) (entryMonomial i j) (-1 : Group n)
  have hneg : ∀ U : Group n, entryMonomial i j ((-1) * U) = -entryMonomial i j U := by
    intro U
    rw [neg_one_mul, entryMonomial_neg, hk.neg_one_pow, neg_one_mul]
  simp_rw [hneg] at heq
  rw [integral_neg] at heq
  change -entryMoment i j = entryMoment i j at heq
  linarith

end FreeProbability.Orthogonal

import FreeProbability.Applications.ReLU.FreshForward
import Mathlib.MeasureTheory.Constructions.Pi

/-! # A finite-depth independent-Haar ReLU forward model

Coordinates are numbered from the output layer backwards. Recursion removes
the output weight, and the finite product Haar law makes that weight independent
of all preceding layers. Positive gains are retained explicitly.
-/

namespace FreeProbability.ReLU

open Matrix MeasureTheory ProbabilityTheory

variable {n : Type*} [Fintype n] [DecidableEq n]

abbrev Weights (n : Type*) [Fintype n] [DecidableEq n] (L : ℕ) := Fin L → Orthogonal.Group n

noncomputable def weightLaw (n : Type*) [Fintype n] [DecidableEq n] (L : ℕ) : Measure (Weights n L) :=
  Measure.pi (fun _ => Orthogonal.haar n)

instance weightLaw_isProbabilityMeasure (L : ℕ) : IsProbabilityMeasure (weightLaw n L) := by
  unfold weightLaw
  infer_instance

noncomputable def forwardState (x : n → ℝ) :
    (L : ℕ) → (Fin L → ℝ) → Weights n L → (n → ℝ)
  | 0, _, _ => x
  | L + 1, σ, W => σ 0 • (fun i => max 0
      (((W 0 : Matrix n n ℝ) *ᵥ forwardState x L (fun j => σ j.succ) (fun j => W j.succ)) i))

noncomputable def forwardPreactivation (x : n → ℝ) (L : ℕ) (σ : Fin (L + 1) → ℝ)
    (W : Weights n (L + 1)) : n → ℝ :=
  (W 0 : Matrix n n ℝ) *ᵥ forwardState x L (fun j => σ j.succ) (fun j => W j.succ)

theorem forwardState_succ (x : n → ℝ) (L : ℕ) (σ : Fin (L + 1) → ℝ) (W : Weights n (L + 1)) :
    forwardState x (L + 1) σ W = σ 0 •
      (gateProjection (forwardPreactivation x L σ W) *ᵥ forwardPreactivation x L σ W) := by
  rw [gateProjection_mulVec]
  rfl

omit [Fintype n] in
theorem gateProjection_smul (a : ℝ) (ha : 0 < a) (v : n → ℝ) :
    gateProjection (a • v) = gateProjection v := by
  unfold gateProjection
  congr 1
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, mul_pos_iff_of_pos_left ha]

/-- The recursive state is the actual ReLU applied to the scaled preactivation. -/
theorem forwardState_succ_scaled (x : n → ℝ) (L : ℕ) (σ : Fin (L + 1) → ℝ)
    (hσ : 0 < σ 0) (W : Weights n (L + 1)) :
    forwardState x (L + 1) σ W = gateProjection (σ 0 • forwardPreactivation x L σ W) *ᵥ
      (σ 0 • forwardPreactivation x L σ W) := by
  rw [gateProjection_smul _ hσ, Matrix.mulVec_smul, forwardState_succ]

omit [Fintype n] [DecidableEq n] in
theorem continuous_reluVector : Continuous (fun v : n → ℝ => (fun i => max 0 (v i))) := by
  fun_prop

theorem measurable_forwardState (x : n → ℝ) (L : ℕ) (σ : Fin L → ℝ) :
    Measurable (forwardState x L σ) := by
  induction L with
  | zero => exact measurable_const
  | succ L ih =>
    have ht : Measurable (fun W : Weights n (L + 1) =>
        forwardState x L (fun j => σ j.succ) (fun j => W j.succ)) :=
      (ih _).comp (measurable_pi_iff.mpr (fun j => measurable_pi_apply j.succ))
    have hp : Measurable (fun W : Weights n (L + 1) =>
        (W 0 : Matrix n n ℝ) *ᵥ forwardState x L (fun j => σ j.succ) (fun j => W j.succ)) :=
      Orthogonal.continuous_action.measurable.comp ((measurable_pi_apply 0).prodMk ht)
    exact (measurable_const_smul (σ 0)).comp (continuous_reluVector.measurable.comp hp)

theorem measurable_forwardPreactivation (x : n → ℝ) (L : ℕ) (σ : Fin (L + 1) → ℝ) :
    Measurable (forwardPreactivation x L σ) := by
  have ht : Measurable (fun W : Weights n (L + 1) =>
      forwardState x L (fun j => σ j.succ) (fun j => W j.succ)) :=
    (measurable_forwardState x L _).comp (measurable_pi_iff.mpr (fun j => measurable_pi_apply j.succ))
  exact Orthogonal.continuous_action.measurable.comp ((measurable_pi_apply 0).prodMk ht)

theorem splitWeights_hasLaw (L : ℕ) :
    HasLaw (fun W : Weights n (L + 1) => ((fun j : Fin L => W j.succ), W 0))
      ((weightLaw n L).prod (Orthogonal.haar n)) (weightLaw n (L + 1)) := by
  have hp := measurePreserving_piFinSuccAbove
    (fun _ : Fin (L + 1) => Orthogonal.haar n) (0 : Fin (L + 1))
  have hs := Measure.measurePreserving_swap (μ := Orthogonal.haar n)
    (ν := Measure.pi (fun _ : Fin L => Orthogonal.haar n))
  exact (hs.comp hp).hasLaw

theorem forwardState_zero_probability_le (x : n → ℝ) (hx : x ≠ 0) (L : ℕ)
    (σ : Fin L → ℝ) (hσ : ∀ i, 0 < σ i) :
    (weightLaw n L) {W | forwardState x L σ W = 0} ≤
      ENNReal.ofReal ((L : ℝ) * (1 / 2 : ℝ) ^ Fintype.card n) := by
  induction L with
  | zero => simp [forwardState, hx]
  | succ L ih =>
    let X := forwardState x L (fun j => σ j.succ)
    have hX : Measurable X := measurable_forwardState x L _
    let S := {p : Weights n L × Orthogonal.Group n |
      gateProjection (Orthogonal.freshHaarImage X p) *ᵥ Orthogonal.freshHaarImage X p = 0}
    have hrelu : Measurable (fun v : n → ℝ => gateProjection v *ᵥ v) := by
      simp only [gateProjection_mulVec]
      exact continuous_reluVector.measurable
    have hS : MeasurableSet S :=
      (hrelu.comp (Orthogonal.measurable_freshHaarImage X hX)) (measurableSet_singleton 0)
    have he : {W : Weights n (L + 1) | forwardState x (L + 1) σ W = 0} =
        {W | gateProjection (forwardPreactivation x L σ W) *ᵥ forwardPreactivation x L σ W = 0} := by
      ext W
      simp only [Set.mem_ofPred_eq, forwardState_succ, smul_eq_zero, (hσ 0).ne', false_or]
    calc
      _ = (weightLaw n (L + 1))
          {W | gateProjection (forwardPreactivation x L σ W) *ᵥ forwardPreactivation x L σ W = 0} :=
        congrArg (weightLaw n (L + 1)) he
      _ = (weightLaw n L).prod (Orthogonal.haar n) S := (splitWeights_hasLaw L).measure_eq hS
      _ ≤ (weightLaw n L) {W | X W = 0} + ENNReal.ofReal ((1 / 2 : ℝ) ^ Fintype.card n) :=
        fresh_haar_gateProjection_mulVec_zero_le _ X hX
      _ ≤ ENNReal.ofReal ((L : ℝ) * (1 / 2 : ℝ) ^ Fintype.card n) +
          ENNReal.ofReal ((1 / 2 : ℝ) ^ Fintype.card n) :=
        add_le_add (ih _ (fun j => hσ j.succ)) le_rfl
      _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        push_cast
        ring

theorem forwardPreactivation_energy_deviation_le (x : n → ℝ) (hx : x ≠ 0) (L : ℕ)
    (σ : Fin (L + 1) → ℝ) (hσ : ∀ i, 0 < σ i) (ε : ℝ) (hε : 0 < ε) :
    (weightLaw n (L + 1)) {W | ε ≤ |Orthogonal.positiveEnergyFraction
      (forwardPreactivation x L σ W) - 1 / 2|} ≤
        ENNReal.ofReal ((L : ℝ) * (1 / 2 : ℝ) ^ Fintype.card n) +
        ENNReal.ofReal (Orthogonal.energyFourthMomentBound /
          ((Fintype.card n : ℝ) ^ 2 * Orthogonal.energyDeviationThreshold ε ^ 4)) := by
  let X := forwardState x L (fun j => σ j.succ)
  have hX : Measurable X := measurable_forwardState x L _
  have hR := Orthogonal.measurable_positiveEnergyFraction.comp (Orthogonal.measurable_freshHaarImage X hX)
  have hS : MeasurableSet {p : Weights n L × Orthogonal.Group n |
      ε ≤ |Orthogonal.positiveEnergyFraction (Orthogonal.freshHaarImage X p) - 1 / 2|} :=
    measurableSet_le measurable_const ((show Measurable (fun a : ℝ => |a|) from
      continuous_id.abs.measurable).comp (hR.sub measurable_const))
  calc
    _ = (weightLaw n L).prod (Orthogonal.haar n) {p | ε ≤
        |Orthogonal.positiveEnergyFraction (Orthogonal.freshHaarImage X p) - 1 / 2|} :=
      (splitWeights_hasLaw L).measure_eq hS
    _ ≤ (weightLaw n L) {W | X W = 0} + _ :=
      Orthogonal.fresh_haar_positiveEnergyFraction_deviation_le _ X hX ε hε
    _ ≤ _ := add_le_add (forwardState_zero_probability_le x hx L _ (fun j => hσ j.succ)) le_rfl

theorem forwardPreactivation_gateRank_deviation_le (x : n → ℝ) (hx : x ≠ 0) (L : ℕ)
    (σ : Fin (L + 1) → ℝ) (hσ : ∀ i, 0 < σ i) (ε : ℝ) (hε : 0 ≤ ε) :
    (weightLaw n (L + 1)) {W | ε ≤ |(Orthogonal.gateRank
      (forwardPreactivation x L σ W) : ℝ) / (Fintype.card n : ℝ) - 1 / 2|} ≤
        ENNReal.ofReal ((L : ℝ) * (1 / 2 : ℝ) ^ Fintype.card n) +
        ENNReal.ofReal (2 * Real.exp (-2 * (Fintype.card n : ℝ) * ε ^ 2)) := by
  let X := forwardState x L (fun j => σ j.succ)
  have hX : Measurable X := measurable_forwardState x L _
  have hB : MeasurableSet {j : ℕ | ε ≤ |(j : ℝ) / (Fintype.card n : ℝ) - 1 / 2|} := .of_discrete
  have hS := (Orthogonal.measurable_gateRank.comp (Orthogonal.measurable_freshHaarImage X hX)) hB
  calc
    _ = (weightLaw n L).prod (Orthogonal.haar n) {p | ε ≤
        |(Orthogonal.gateRank (Orthogonal.freshHaarImage X p) : ℝ) / (Fintype.card n : ℝ) - 1 / 2|} :=
      (splitWeights_hasLaw L).measure_eq hS
    _ ≤ (weightLaw n L) {W | X W = 0} + _ :=
      Orthogonal.fresh_haar_gateRank_deviation_le _ X hX ε hε
    _ ≤ _ := add_le_add (forwardState_zero_probability_le x hx L _ (fun j => hσ j.succ)) le_rfl

end FreeProbability.ReLU

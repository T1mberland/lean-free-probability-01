import FreeProbability.Applications.ReLU.ForwardModel

/-! # Independent random initial inputs in the finite-depth Haar model -/

namespace FreeProbability.ReLU

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem continuous_joint_forwardState (L : ℕ) (σ : Fin L → ℝ) :
    Continuous (fun p : (n → ℝ) × Weights n L => forwardState p.1 L σ p.2) := by
  induction L with
  | zero => exact continuous_fst
  | succ L ih =>
    have ht : Continuous (fun p : (n → ℝ) × Weights n (L + 1) =>
        (p.1, fun j : Fin L => p.2 j.succ)) :=
      continuous_fst.prodMk (continuous_pi (fun j => (continuous_apply j.succ).comp continuous_snd))
    have hy := (ih (fun j => σ j.succ)).comp ht
    have hp := Orthogonal.continuous_action.comp
      (((continuous_apply 0).comp continuous_snd).prodMk hy)
    exact (continuous_reluVector.comp hp).const_smul (σ 0)

theorem continuous_joint_forwardPreactivation (L : ℕ) (σ : Fin (L + 1) → ℝ) :
    Continuous (fun p : (n → ℝ) × Weights n (L + 1) => forwardPreactivation p.1 L σ p.2) := by
  have ht : Continuous (fun p : (n → ℝ) × Weights n (L + 1) =>
      (p.1, fun j : Fin L => p.2 j.succ)) :=
    continuous_fst.prodMk (continuous_pi (fun j => (continuous_apply j.succ).comp continuous_snd))
  have hy := (continuous_joint_forwardState L (fun j => σ j.succ)).comp ht
  exact Orthogonal.continuous_action.comp (((continuous_apply 0).comp continuous_snd).prodMk hy)

variable {Θ : Type*} [MeasurableSpace Θ]

noncomputable def randomForwardState (X : Θ → (n → ℝ)) (L : ℕ) (σ : Fin L → ℝ)
    (p : Θ × Weights n L) : n → ℝ := forwardState (X p.1) L σ p.2

noncomputable def randomForwardPreactivation (X : Θ → (n → ℝ)) (L : ℕ) (σ : Fin (L + 1) → ℝ)
    (p : Θ × Weights n (L + 1)) : n → ℝ := forwardPreactivation (X p.1) L σ p.2

theorem measurable_randomForwardState (X : Θ → (n → ℝ)) (hX : Measurable X) (L : ℕ) (σ : Fin L → ℝ) :
    Measurable (randomForwardState X L σ) :=
  (continuous_joint_forwardState L σ).measurable.comp ((hX.comp measurable_fst).prodMk measurable_snd)

theorem measurable_randomForwardPreactivation (X : Θ → (n → ℝ)) (hX : Measurable X)
    (L : ℕ) (σ : Fin (L + 1) → ℝ) : Measurable (randomForwardPreactivation X L σ) :=
  (continuous_joint_forwardPreactivation L σ).measurable.comp ((hX.comp measurable_fst).prodMk measurable_snd)

theorem randomForwardState_zero_probability_le (ν : Measure Θ) [IsProbabilityMeasure ν]
    (X : Θ → (n → ℝ)) (hX : Measurable X) (hx : ∀ᵐ θ ∂ν, X θ ≠ 0)
    (L : ℕ) (σ : Fin L → ℝ) (hσ : ∀ i, 0 < σ i) :
    ν.prod (weightLaw n L) {p | randomForwardState X L σ p = 0} ≤
      ENNReal.ofReal ((L : ℝ) * (1 / 2 : ℝ) ^ Fintype.card n) := by
  have hm : MeasurableSet {p : Θ × Weights n L | randomForwardState X L σ p = 0} :=
    (measurable_randomForwardState X hX L σ) (measurableSet_singleton 0)
  have hD : ν {θ | X θ = 0} = 0 := by simpa only [not_not] using ae_iff.mp hx
  have h := measure_prod_event_le_of_fiber_bound ν (weightLaw n L) _ hm
    {θ | X θ = 0} (hX (measurableSet_singleton 0))
    (ENNReal.ofReal ((L : ℝ) * (1 / 2 : ℝ) ^ Fintype.card n))
    (fun θ hθ => forwardState_zero_probability_le (X θ) hθ L σ hσ)
  simpa only [hD, zero_add] using h

theorem randomForwardPreactivation_energy_deviation_le (ν : Measure Θ) [IsProbabilityMeasure ν]
    (X : Θ → (n → ℝ)) (hX : Measurable X) (hx : ∀ᵐ θ ∂ν, X θ ≠ 0)
    (L : ℕ) (σ : Fin (L + 1) → ℝ) (hσ : ∀ i, 0 < σ i) (ε : ℝ) (hε : 0 < ε) :
    ν.prod (weightLaw n (L + 1)) {p | ε ≤
      |Orthogonal.positiveEnergyFraction (randomForwardPreactivation X L σ p) - 1 / 2|} ≤
        ENNReal.ofReal ((L : ℝ) * (1 / 2 : ℝ) ^ Fintype.card n) +
        ENNReal.ofReal (Orthogonal.energyFourthMomentBound /
          ((Fintype.card n : ℝ) ^ 2 * Orthogonal.energyDeviationThreshold ε ^ 4)) := by
  have hR := Orthogonal.measurable_positiveEnergyFraction.comp (measurable_randomForwardPreactivation X hX L σ)
  have hm : MeasurableSet {p : Θ × Weights n (L + 1) | ε ≤
      |Orthogonal.positiveEnergyFraction (randomForwardPreactivation X L σ p) - 1 / 2|} :=
    measurableSet_le measurable_const ((show Measurable (fun a : ℝ => |a|) from
      continuous_id.abs.measurable).comp (hR.sub measurable_const))
  have hD : ν {θ | X θ = 0} = 0 := by simpa only [not_not] using ae_iff.mp hx
  have h := measure_prod_event_le_of_fiber_bound ν (weightLaw n (L + 1)) _ hm
    {θ | X θ = 0} (hX (measurableSet_singleton 0)) _
    (fun θ hθ => forwardPreactivation_energy_deviation_le (X θ) hθ L σ hσ ε hε)
  simpa only [hD, zero_add] using h

theorem randomForwardPreactivation_gateRank_deviation_le (ν : Measure Θ) [IsProbabilityMeasure ν]
    (X : Θ → (n → ℝ)) (hX : Measurable X) (hx : ∀ᵐ θ ∂ν, X θ ≠ 0)
    (L : ℕ) (σ : Fin (L + 1) → ℝ) (hσ : ∀ i, 0 < σ i) (ε : ℝ) (hε : 0 ≤ ε) :
    ν.prod (weightLaw n (L + 1)) {p | ε ≤
      |(Orthogonal.gateRank (randomForwardPreactivation X L σ p) : ℝ) / (Fintype.card n : ℝ) - 1 / 2|} ≤
        ENNReal.ofReal ((L : ℝ) * (1 / 2 : ℝ) ^ Fintype.card n) +
        ENNReal.ofReal (2 * Real.exp (-2 * (Fintype.card n : ℝ) * ε ^ 2)) := by
  have hB : MeasurableSet {j : ℕ | ε ≤ |(j : ℝ) / (Fintype.card n : ℝ) - 1 / 2|} := .of_discrete
  have hm : MeasurableSet {p : Θ × Weights n (L + 1) | ε ≤
      |(Orthogonal.gateRank (randomForwardPreactivation X L σ p) : ℝ) / (Fintype.card n : ℝ) - 1 / 2|} :=
    (Orthogonal.measurable_gateRank.comp (measurable_randomForwardPreactivation X hX L σ)) hB
  have hD : ν {θ | X θ = 0} = 0 := by simpa only [not_not] using ae_iff.mp hx
  have h := measure_prod_event_le_of_fiber_bound ν (weightLaw n (L + 1)) _ hm
    {θ | X θ = 0} (hX (measurableSet_singleton 0)) _
    (fun θ hθ => forwardPreactivation_gateRank_deviation_le (X θ) hθ L σ hσ ε hε)
  simpa only [hD, zero_add] using h

end FreeProbability.ReLU

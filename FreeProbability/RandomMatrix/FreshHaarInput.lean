import FreeProbability.RandomMatrix.ProductFiberLaw
import FreeProbability.RandomMatrix.HaarSignEnergy
import FreeProbability.RandomMatrix.GateConcentration

/-! # Fresh Haar weights acting on measurable random inputs

The past and fresh weight have a genuine product law. Constant nonzero-input
fiber laws give independence from the past. Concentration retains the probability
of an already vanishing input explicitly.
-/

namespace FreeProbability.Orthogonal

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {n : Type*} [Fintype n] [DecidableEq n]

noncomputable def freshHaarImage (X : Ω → (n → ℝ)) (p : Ω × Group n) : n → ℝ :=
  (p.2 : Matrix n n ℝ) *ᵥ X p.1

theorem measurable_freshHaarImage (X : Ω → (n → ℝ)) (hX : Measurable X) :
    Measurable (freshHaarImage X) := by
  exact continuous_action.measurable.comp (measurable_snd.prodMk (hX.comp measurable_fst))

theorem haar_direction_hasLaw (x : n → ℝ) (hx : x ≠ 0) :
    HasLaw (fun U : Group n => direction ((U : Matrix n n ℝ) *ᵥ x)) (gaussianDirection n) (haar n) := by
  obtain ⟨i, _⟩ := Function.ne_iff.mp hx
  let _ : Nonempty n := ⟨i⟩
  refine ⟨(measurable_direction.comp (continuous_mulVec x).measurable).aemeasurable, ?_⟩
  have he : (fun U : Group n => direction ((U : Matrix n n ℝ) *ᵥ x)) =
      (fun U : Group n => (U : Matrix n n ℝ) *ᵥ direction x) := by
    funext U
    exact direction_mulVec U x
  rw [he]
  exact (gaussianDirection_eq_vectorLaw (direction x) (norm_direction x hx)).symm

/-- The full normalized fresh image, not just scalar statistics, is independent
of the past on almost-surely nonzero inputs. -/
theorem fresh_haar_direction_joint_hasLaw (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → (n → ℝ)) (hX : Measurable X) (hx : ∀ᵐ ω ∂μ, X ω ≠ 0) :
    HasLaw (fun p : Ω × Group n => (p.1, direction (freshHaarImage X p)))
      (μ.prod (gaussianDirection n)) (μ.prod (haar n)) := by
  apply hasLaw_prod_fst_of_fiber_law μ (haar n) _ _
    (measurable_direction.comp (measurable_freshHaarImage X hX))
  filter_upwards [hx] with ω hω
  exact haar_direction_hasLaw (X ω) hω

/-- The gate count of a fresh Haar image of an almost-surely nonzero past input
has its binomial law jointly and independently of the entire past. -/
theorem fresh_haar_gateRank_joint_hasLaw (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → (n → ℝ)) (hX : Measurable X) (hx : ∀ᵐ ω ∂μ, X ω ≠ 0) :
    HasLaw (fun p : Ω × Group n => (p.1, gateRank (freshHaarImage X p)))
      (μ.prod (binomial (Fintype.card n) halfProbability)) (μ.prod (haar n)) := by
  apply hasLaw_prod_fst_of_fiber_law μ (haar n) _ _
    (measurable_gateRank.comp (measurable_freshHaarImage X hX))
  filter_upwards [hx] with ω hω
  exact gateRank_haar_hasLaw (X ω) hω

/-- The energy fraction also has a constant full law jointly with the past. -/
theorem fresh_haar_positiveEnergyFraction_joint_hasLaw (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → (n → ℝ)) (hX : Measurable X) (hx : ∀ᵐ ω ∂μ, X ω ≠ 0) :
    HasLaw (fun p : Ω × Group n => (p.1, positiveEnergyFraction (freshHaarImage X p)))
      (μ.prod ((gaussianVector n).map positiveEnergyFraction)) (μ.prod (haar n)) := by
  let _ : IsProbabilityMeasure ((gaussianVector n).map positiveEnergyFraction) :=
    (Measure.isProbabilityMeasure_map_iff measurable_positiveEnergyFraction.aemeasurable).mpr inferInstance
  apply hasLaw_prod_fst_of_fiber_law μ (haar n) _ _
    (measurable_positiveEnergyFraction.comp (measurable_freshHaarImage X hX))
  filter_upwards [hx] with ω hω
  exact haar_positiveEnergyFraction_hasLaw (X ω) hω

/-- No almost-sure nonzero-input hypothesis is imposed: already extinct inputs
are kept as an explicit error probability. -/
theorem fresh_haar_positiveEnergyFraction_deviation_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → (n → ℝ)) (hX : Measurable X) (ε : ℝ) (hε : 0 < ε) :
    μ.prod (haar n) {p | ε ≤ |positiveEnergyFraction (freshHaarImage X p) - 1 / 2|} ≤
      μ {ω | X ω = 0} + ENNReal.ofReal (energyFourthMomentBound /
        ((Fintype.card n : ℝ) ^ 2 * energyDeviationThreshold ε ^ 4)) := by
  have hR := measurable_positiveEnergyFraction.comp (measurable_freshHaarImage X hX)
  have hm : MeasurableSet {p : Ω × Group n | ε ≤ |positiveEnergyFraction (freshHaarImage X p) - 1 / 2|} :=
    measurableSet_le measurable_const ((show Measurable (fun a : ℝ => |a|) from
      continuous_id.abs.measurable).comp (hR.sub measurable_const))
  apply measure_prod_event_le_of_fiber_bound μ (haar n) _ hm _ (hX (measurableSet_singleton 0)) _
  intro ω hω
  exact haar_positiveEnergyFraction_deviation_le (X ω) hω ε hε

theorem fresh_haar_gateRank_deviation_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → (n → ℝ)) (hX : Measurable X) (ε : ℝ) (hε : 0 ≤ ε) :
    μ.prod (haar n) {p | ε ≤ |(gateRank (freshHaarImage X p) : ℝ) /
      (Fintype.card n : ℝ) - 1 / 2|} ≤
        μ {ω | X ω = 0} + ENNReal.ofReal (2 * Real.exp (-2 * (Fintype.card n : ℝ) * ε ^ 2)) := by
  have hB : MeasurableSet {j : ℕ | ε ≤ |(j : ℝ) / (Fintype.card n : ℝ) - 1 / 2|} := .of_discrete
  have hm := (measurable_gateRank.comp (measurable_freshHaarImage X hX)) hB
  apply measure_prod_event_le_of_fiber_bound μ (haar n) _ hm _ (hX (measurableSet_singleton 0)) _
  intro ω hω
  have h := ENNReal.ofReal_le_ofReal (haar_gateRank_deviation_le (X ω) hω ε hε)
  rw [ofReal_measureReal (μ := haar n)] at h
  exact h

end FreeProbability.Orthogonal

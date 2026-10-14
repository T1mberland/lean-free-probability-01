import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.Instances.Real.Lemmas

/-! # Almost-sure limits from summable deviations, without cross-index independence -/

namespace FreeProbability

open MeasureTheory Filter
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The first Borel--Cantelli lemma converts summable deviations to a real
almost-sure limit. No independence between indices is needed. -/
theorem ae_tendsto_zero_of_summable_deviations (μ : Measure Ω) (f : ℕ → Ω → ℝ)
    (h : ∀ ε : ℝ, 0 < ε → (∑' k, μ {ω | ε ≤ |f k ω|}) ≠ ∞) :
    ∀ᵐ ω ∂μ, Tendsto (fun k => f k ω) atTop (nhds 0) := by
  have hq (j : ℕ) : ∀ᵐ ω ∂μ, ∀ᶠ k in atTop, |f k ω| < 1 / ((j : ℝ) + 1) := by
    have hpos : 0 < 1 / ((j : ℝ) + 1) := by positivity
    have ha := ae_eventually_notMem (h _ hpos)
    filter_upwards [ha] with ω hω
    filter_upwards [hω] with k hk
    exact lt_of_not_ge hk
  have hall : ∀ᵐ ω ∂μ, ∀ j : ℕ, ∀ᶠ k in atTop, |f k ω| < 1 / ((j : ℝ) + 1) :=
    ae_all_iff.mpr hq
  filter_upwards [hall] with ω hω
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
  filter_upwards [hω j] with k hk
  simpa [Real.dist_eq] using hk.trans hj

end FreeProbability

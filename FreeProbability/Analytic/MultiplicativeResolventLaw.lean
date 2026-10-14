import FreeProbability.Analytic.MultiplicativeResolventSandwich
import FreeProbability.Analytic.SpectralMeasureConvergence
import FreeProbability.Analytic.SpectralMeasureSupport

/-! # Actual positive multiplicative spectral probability laws

The law is that of the actual square-root sandwich in the given probability
space. No construction of a free realization of arbitrary input measures is
asserted here.
-/

noncomputable section
open MeasureTheory
namespace FreeProbability
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The genuine probability law of the actual positive multiplication model. -/
def positiveMultiplicativeProbabilityLaw (φ : StarProbabilitySpace A)
    (a b : A) (hb : 0 ≤ b) : ProbabilityMeasure ℝ :=
  spectralProbabilityMeasure φ (positiveMultiplicativeSandwich_nonneg a b hb).isSelfAdjoint

/-- The actual positive law is supported on the nonnegative real line, without
faithfulness of the state. -/
theorem positiveMultiplicativeProbabilityLaw_support_nonneg (φ : StarProbabilitySpace A)
    (a b : A) (hb : 0 ≤ b) :
    (positiveMultiplicativeProbabilityLaw φ a b hb : Measure ℝ).support ⊆ Set.Ici 0 := by
  intro x hx
  have hs := spectralMeasure_support_subset φ
    (positiveMultiplicativeSandwich_nonneg a b hb).isSelfAdjoint hx
  exact spectrum_nonneg_of_nonneg (positiveMultiplicativeSandwich_nonneg a b hb) hs

/-- The actual positive law has compact support, without a faithful-state premise. -/
theorem positiveMultiplicativeProbabilityLaw_isCompact_support (φ : StarProbabilitySpace A)
    (a b : A) (hb : 0 ≤ b) :
    IsCompact (positiveMultiplicativeProbabilityLaw φ a b hb : Measure ℝ).support := by
  apply (ContinuousFunctionalCalculus.isCompact_spectrum (positiveMultiplicativeSandwich a b)).of_isClosed_subset
    Measure.isClosed_support
  exact spectralMeasure_support_subset φ (positiveMultiplicativeSandwich_nonneg a b hb).isSelfAdjoint

/-- Under a trace the actual positive law has exactly the ordered product moments. -/
theorem positiveMultiplicativeProbabilityLaw_power_moment (φ : StarProbabilitySpace A)
    (hφ : IsTracial φ.toProbabilitySpace) (a b : A) (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    φ.expectation ((a * b) ^ n) =
      (∫ x : ℝ, x ^ n ∂(positiveMultiplicativeProbabilityLaw φ a b hb : Measure ℝ) : ℝ) := by
  rw [← φ.expectation_pow_positiveMultiplicativeSandwich hφ a b ha n]
  exact spectralMeasure_power_moment φ (positiveMultiplicativeSandwich_nonneg a b hb).isSelfAdjoint n

end FreeProbability

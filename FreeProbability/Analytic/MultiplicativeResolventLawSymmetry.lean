import FreeProbability.Analytic.MultiplicativeResolventLaw

/-! # Actual positive multiplication laws: symmetry and units -/

noncomputable section
open MeasureTheory
namespace FreeProbability
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Actual positive multiplication laws commute under a trace, even before
imposing freeness or nonzero first moments. -/
theorem positiveMultiplicativeProbabilityLaw_comm (φ : StarProbabilitySpace A)
    (hφ : IsTracial φ.toProbabilitySpace) (a b : A) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    positiveMultiplicativeProbabilityLaw φ a b hb = positiveMultiplicativeProbabilityLaw φ b a ha := by
  apply Subtype.ext
  apply spectralMeasure_eq_of_power_moments
  intro n
  rw [φ.expectation_pow_positiveMultiplicativeSandwich hφ a b ha,
    φ.expectation_pow_positiveMultiplicativeSandwich hφ b a hb]
  exact hφ.expectation_pow_mul a b n

/-- The literal unit in the first factor leaves the actual positive model unchanged. -/
theorem positiveMultiplicativeSandwich_one_left (b : A) :
    positiveMultiplicativeSandwich (1 : A) b = b := by
  simp [positiveMultiplicativeSandwich]

/-- The literal unit in the second factor leaves a positive variable unchanged. -/
theorem positiveMultiplicativeSandwich_one_right (a : A) (ha : 0 ≤ a) :
    positiveMultiplicativeSandwich a (1 : A) = a := by
  simpa only [positiveMultiplicativeSandwich, mul_one] using CFC.sqrt_mul_sqrt_self a ha

/-- The first-factor unit gives the original genuine spectral probability law. -/
theorem positiveMultiplicativeProbabilityLaw_one_left (φ : StarProbabilitySpace A)
    (b : A) (hb : 0 ≤ b) :
    positiveMultiplicativeProbabilityLaw φ (1 : A) b hb = spectralProbabilityMeasure φ hb.isSelfAdjoint := by
  apply Subtype.ext
  apply spectralMeasure_eq_of_power_moments
  intro n
  rw [positiveMultiplicativeSandwich_one_left]

/-- The second-factor unit gives the original genuine spectral probability law. -/
theorem positiveMultiplicativeProbabilityLaw_one_right (φ : StarProbabilitySpace A)
    (a : A) (ha : 0 ≤ a) :
    positiveMultiplicativeProbabilityLaw φ a (1 : A) zero_le_one = spectralProbabilityMeasure φ ha.isSelfAdjoint := by
  apply Subtype.ext
  apply spectralMeasure_eq_of_power_moments
  intro n
  rw [positiveMultiplicativeSandwich_one_right a ha]
end FreeProbability

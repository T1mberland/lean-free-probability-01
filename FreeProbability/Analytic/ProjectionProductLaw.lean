import FreeProbability.Analytic.ProjectionProductRational
import FreeProbability.Analytic.MultiplicativeResolventLaw

/-! # Genuine compact probability laws of finite positive and projection products -/

noncomputable section
open MeasureTheory
namespace FreeProbability
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The actual probability law of the finite positive product in the supplied
probability space; no universal realization is assumed. -/
def iteratedPositiveProbabilityLaw (φ : StarProbabilitySpace A) (n : ℕ) (p : Fin n → A)
    (hp : ∀ i, 0 ≤ p i) : ProbabilityMeasure ℝ :=
  spectralProbabilityMeasure φ (iteratedPositiveProduct_nonneg n p hp).isSelfAdjoint

/-- The law of the actual finite product has nonnegative support. -/
theorem iteratedPositiveProbabilityLaw_support_nonneg (φ : StarProbabilitySpace A)
    (n : ℕ) (p : Fin n → A) (hp : ∀ i, 0 ≤ p i) :
    (iteratedPositiveProbabilityLaw φ n p hp : Measure ℝ).support ⊆ Set.Ici 0 := by
  intro x hx
  exact spectrum_nonneg_of_nonneg (iteratedPositiveProduct_nonneg n p hp)
    (spectralMeasure_support_subset φ (iteratedPositiveProduct_nonneg n p hp).isSelfAdjoint hx)

/-- The law of the actual finite product has compact support without faithfulness. -/
theorem iteratedPositiveProbabilityLaw_isCompact_support (φ : StarProbabilitySpace A)
    (n : ℕ) (p : Fin n → A) (hp : ∀ i, 0 ≤ p i) :
    IsCompact (iteratedPositiveProbabilityLaw φ n p hp : Measure ℝ).support := by
  apply (ContinuousFunctionalCalculus.isCompact_spectrum (iteratedPositiveProduct n p)).of_isClosed_subset
    Measure.isClosed_support
  exact spectralMeasure_support_subset φ (iteratedPositiveProduct_nonneg n p hp).isSelfAdjoint

/-- Literal powers of the actual product are the power moments of its law. -/
theorem iteratedPositiveProbabilityLaw_power_moment (φ : StarProbabilitySpace A)
    (n : ℕ) (p : Fin n → A) (hp : ∀ i, 0 ≤ p i) (k : ℕ) :
    φ.expectation (iteratedPositiveProduct n p ^ k) =
      (∫ x : ℝ, x ^ k ∂(iteratedPositiveProbabilityLaw φ n p hp : Measure ℝ) : ℝ) :=
  spectralMeasure_power_moment φ (iteratedPositiveProduct_nonneg n p hp).isSelfAdjoint k

/-- The actual iterated projection product is a positive contraction. -/
theorem iteratedProjectionProduct_le_one (n : ℕ) (p : Fin n → A)
    (hp : ∀ i, IsStarProjection (p i)) : iteratedPositiveProduct n p ≤ 1 := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    let a := iteratedPositiveProduct n (fun i => p i.castSucc)
    have ha : 0 ≤ a := iteratedPositiveProduct_nonneg n _ (fun i => (hp i.castSucc).nonneg)
    have hs := (CFC.sqrt_nonneg a).isSelfAdjoint
    have hle := star_left_conjugate_le_conjugate (hp (Fin.last n)).le_one (CFC.sqrt a)
    simp only [hs.star_eq, mul_one, CFC.sqrt_mul_sqrt_self a ha] at hle
    exact hle.trans (ih (fun i => p i.castSucc) (fun i => hp i.castSucc))

/-- The actual projection-product law is supported on the unit interval.
This bound does not identify its sharper right edge. -/
theorem iteratedProjectionProbabilityLaw_support_unitInterval (φ : StarProbabilitySpace A)
    (n : ℕ) (p : Fin n → A) (hp : ∀ i, IsStarProjection (p i)) :
    (iteratedPositiveProbabilityLaw φ n p (fun i => (hp i).nonneg) : Measure ℝ).support ⊆
      Set.Icc 0 1 := by
  intro x hx
  have hs := spectralMeasure_support_subset φ
    (iteratedPositiveProduct_nonneg n p (fun i => (hp i).nonneg)).isSelfAdjoint hx
  refine ⟨spectrum_nonneg_of_nonneg (iteratedPositiveProduct_nonneg n p (fun i => (hp i).nonneg)) hs, ?_⟩
  have hb : iteratedPositiveProduct n p ≤ algebraMap ℝ A 1 := by
    simpa using iteratedProjectionProduct_le_one n p hp
  exact ((le_algebraMap_iff_spectrum_le
    (iteratedPositiveProduct_nonneg n p (fun i => (hp i).nonneg)).isSelfAdjoint).mp hb) x hs
end FreeProbability

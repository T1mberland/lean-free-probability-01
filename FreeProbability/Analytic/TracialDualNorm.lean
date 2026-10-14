import FreeProbability.Analytic.TracialAbsoluteValue
import Mathlib.Analysis.Normed.Operator.Mul

/-! # The genuine trace pairing into the continuous dual

The pairing `J(T)(S) = τ(ST)` is continuous for the original operator norm.
Faithfulness makes this map injective. Its identification with the positive
absolute-value trace size is a separate mathematical obligation.
-/

namespace FreeProbability

open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Continuous dual-valued trace pairing, with the order of factors fixed. -/
noncomputable def tracialDualEmbedding (φ : StarProbabilitySpace A) :
    A →L[ℂ] (A →L[ℂ] ℂ) :=
  (ContinuousLinearMap.compL ℂ A A ℂ φ.continuousExpectation).comp
    (ContinuousLinearMap.mul ℂ A).flip

@[simp] theorem tracialDualEmbedding_apply (φ : StarProbabilitySpace A) (T S : A) :
    tracialDualEmbedding φ T S = φ.expectation (S * T) := rfl

theorem tracialDualEmbedding_norm_le (φ : StarProbabilitySpace A) (T : A) :
    ‖tracialDualEmbedding φ T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro S
  exact (φ.expectation_norm_le (S * T)).trans
    ((norm_mul_le S T).trans_eq (mul_comm _ _))

theorem tracialDualEmbedding_opNorm_le (φ : StarProbabilitySpace A) :
    ‖tracialDualEmbedding φ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro T
  simpa using tracialDualEmbedding_norm_le φ T

theorem tracialDualEmbedding_injective (φ : StarProbabilitySpace A)
    (hφ : IsFaithful φ.toProbabilitySpace) : Function.Injective (tracialDualEmbedding φ) := by
  intro T U h
  have hz : tracialDualEmbedding φ (T - U) = 0 := by rw [map_sub, h, sub_self]
  have he := congrArg (fun f : A →L[ℂ] ℂ => f (star (T - U))) hz
  change φ.expectation (star (T - U) * (T - U)) = 0 at he
  exact sub_eq_zero.mp (hφ (T - U) he)

theorem tracialDualEmbedding_symmetric (φ : StarProbabilitySpace A)
    (hφ : IsTracial φ.toProbabilitySpace) (T S : A) :
    tracialDualEmbedding φ T S = tracialDualEmbedding φ S T := hφ S T

/-- The pulled-back dual norm has a triangle inequality, independently of the
still separate absolute-value norm identification. -/
theorem tracialDualEmbedding_norm_add_le (φ : StarProbabilitySpace A) (T U : A) :
    ‖tracialDualEmbedding φ (T + U)‖ ≤
      ‖tracialDualEmbedding φ T‖ + ‖tracialDualEmbedding φ U‖ := by
  rw [map_add]
  exact norm_add_le _ _

end FreeProbability

import FreeProbability.Analytic.Expectation
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! # Absolute value and the positive trace size

These are the actual CFC absolute value and its expectation. No triangle
inequality or identification with a dual norm is assumed here.
-/

namespace FreeProbability

open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The positive square root of `T* T` in the original C-star algebra. -/
noncomputable def tracialAbsoluteValue (T : A) : A := CFC.sqrt (star T * T)

theorem tracialAbsoluteValue_nonneg (T : A) : 0 ≤ tracialAbsoluteValue T :=
  CFC.sqrt_nonneg _

theorem tracialAbsoluteValue_selfAdjoint (T : A) :
    IsSelfAdjoint (tracialAbsoluteValue T) :=
  IsSelfAdjoint.of_nonneg (tracialAbsoluteValue_nonneg T)

theorem tracialAbsoluteValue_mul_self (T : A) :
    tracialAbsoluteValue T * tracialAbsoluteValue T = star T * T :=
  CFC.sqrt_mul_sqrt_self _ (star_mul_self_nonneg T)

@[simp] theorem tracialAbsoluteValue_zero : tracialAbsoluteValue (0 : A) = 0 := by
  simp [tracialAbsoluteValue]

@[simp] theorem tracialAbsoluteValue_eq_zero_iff (T : A) :
    tracialAbsoluteValue T = 0 ↔ T = 0 := by
  rw [tracialAbsoluteValue, CFC.sqrt_eq_zero_iff _ (star_mul_self_nonneg T)]
  exact CStarRing.star_mul_self_eq_zero_iff T

@[simp] theorem tracialAbsoluteValue_norm (T : A) :
    ‖tracialAbsoluteValue T‖ = ‖T‖ := by
  have h := congrArg norm (tracialAbsoluteValue_mul_self T)
  rw [(tracialAbsoluteValue_selfAdjoint T).norm_mul_self,
    CStarRing.norm_star_mul_self] at h
  nlinarith [norm_nonneg (tracialAbsoluteValue T), norm_nonneg T]

/-- The real expectation of the genuine positive absolute value. -/
noncomputable def tracialSize (φ : StarProbabilitySpace A) (T : A) : ℝ :=
  (φ.expectation (tracialAbsoluteValue T)).re

theorem tracialSize_nonneg (φ : StarProbabilitySpace A) (T : A) :
    0 ≤ tracialSize φ T :=
  (φ.expectation_nonneg (tracialAbsoluteValue_nonneg T)).1

theorem expectation_tracialAbsoluteValue (φ : StarProbabilitySpace A) (T : A) :
    φ.expectation (tracialAbsoluteValue T) = (tracialSize φ T : ℂ) := by
  apply Complex.ext
  · rfl
  · exact φ.expectation_selfAdjoint_im_eq_zero
      (tracialAbsoluteValue_selfAdjoint T).star_eq

theorem tracialSize_le_norm (φ : StarProbabilitySpace A) (T : A) :
    tracialSize φ T ≤ ‖T‖ := by
  calc
    tracialSize φ T ≤ ‖φ.expectation (tracialAbsoluteValue T)‖ := Complex.re_le_norm _
    _ ≤ ‖tracialAbsoluteValue T‖ := φ.expectation_norm_le _
    _ = ‖T‖ := tracialAbsoluteValue_norm T

@[simp] theorem tracialSize_zero (φ : StarProbabilitySpace A) :
    tracialSize φ (0 : A) = 0 := by simp [tracialSize]

theorem tracialSize_eq_zero_iff (φ : StarProbabilitySpace A)
    (hφ : IsFaithful φ.toProbabilitySpace) (T : A) :
    tracialSize φ T = 0 ↔ T = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ tracialSize_zero φ⟩
  have he : φ.expectation (tracialAbsoluteValue T) = 0 := by
    rw [expectation_tracialAbsoluteValue, h, Complex.ofReal_zero]
  have hs : CFC.sqrt (tracialAbsoluteValue T) = 0 := by
    apply hφ
    rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)).star_eq,
      CFC.sqrt_mul_sqrt_self _ (tracialAbsoluteValue_nonneg T)]
    exact he
  exact (tracialAbsoluteValue_eq_zero_iff T).mp
    ((CFC.sqrt_eq_zero_iff _ (tracialAbsoluteValue_nonneg T)).mp hs)

end FreeProbability

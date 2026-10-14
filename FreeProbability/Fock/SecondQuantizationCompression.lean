import FreeProbability.Fock.SecondQuantizationIsometry
import Mathlib.Analysis.InnerProductSpace.Positive

/-! # Actual bounded-operator compression by second-quantized isometries -/
noncomputable section
open scoped InnerProductSpace

namespace FreeProbability.Fock
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Actual compression Γ(V)† T Γ(V), defined on the full bounded-operator algebra. -/
def secondQuantizationCompression (V : H →ₗᵢ[ℂ] K) :
    (TensorFullFock K →L[ℂ] TensorFullFock K) →ₗ[ℂ]
      (TensorFullFock H →L[ℂ] TensorFullFock H) where
  toFun T := (secondQuantizationIsometry V).toContinuousLinearMap.adjoint.comp
    (T.comp (secondQuantizationIsometry V).toContinuousLinearMap)
  map_add' T S := by ext f; simp
  map_smul' c T := by ext f; simp

/-- The full-space isometry has actual adjoint left inverse. -/
theorem secondQuantizationIsometry_adjoint_comp (V : H →ₗᵢ[ℂ] K) :
    (secondQuantizationIsometry V).toContinuousLinearMap.adjoint.comp
      (secondQuantizationIsometry V).toContinuousLinearMap = 1 :=
  (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp
    (secondQuantizationIsometry V).norm_map

@[simp] theorem secondQuantizationCompression_one (V : H →ₗᵢ[ℂ] K) :
    secondQuantizationCompression V 1 = 1 := by
  change (secondQuantizationIsometry V).toContinuousLinearMap.adjoint.comp
    ((1 : TensorFullFock K →L[ℂ] TensorFullFock K).comp
      (secondQuantizationIsometry V).toContinuousLinearMap) = 1
  have hi : (1 : TensorFullFock K →L[ℂ] TensorFullFock K).comp
      (secondQuantizationIsometry V).toContinuousLinearMap =
      (secondQuantizationIsometry V).toContinuousLinearMap := rfl
  rw [hi]
  exact secondQuantizationIsometry_adjoint_comp V


/-- Genuine operator norm contraction for every bounded operator. -/
theorem norm_secondQuantizationCompression_le (V : H →ₗᵢ[ℂ] K)
    (T : TensorFullFock K →L[ℂ] TensorFullFock K) :
    ‖secondQuantizationCompression V T‖ ≤ ‖T‖ := by
  let W := (secondQuantizationIsometry V).toContinuousLinearMap
  have hw : ‖W‖ ≤ 1 := (secondQuantizationIsometry V).norm_toContinuousLinearMap_le
  have hwa : ‖W.adjoint‖ ≤ 1 := by rw [ContinuousLinearMap.adjoint.norm_map]; exact hw
  calc
    ‖secondQuantizationCompression V T‖ ≤ ‖W.adjoint‖ * (‖T‖ * ‖W‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖T‖ * 1) := mul_le_mul hwa
      (mul_le_mul_of_nonneg_left hw (norm_nonneg T)) (by positivity) (by positivity)
    _ = ‖T‖ := by ring

/-- Positivity is genuine Hilbert-operator positivity, for arbitrary positive input. -/
theorem secondQuantizationCompression_isPositive (V : H →ₗᵢ[ℂ] K)
    (T : TensorFullFock K →L[ℂ] TensorFullFock K) (hT : T.IsPositive) :
    (secondQuantizationCompression V T).IsPositive := by
  exact hT.adjoint_conj (secondQuantizationIsometry V).toContinuousLinearMap

/-- The compression preserves actual vacuum expectation. -/
theorem secondQuantizationCompression_vacuum_expectation (V : H →ₗᵢ[ℂ] K)
    (T : TensorFullFock K →L[ℂ] TensorFullFock K) :
    inner ℂ (tensorVacuum H) (secondQuantizationCompression V T (tensorVacuum H)) =
      inner ℂ (tensorVacuum K) (T (tensorVacuum K)) := by
  change inner ℂ (tensorVacuum H)
    ((secondQuantizationIsometry V).toContinuousLinearMap.adjoint
      (T (secondQuantizationIsometry V (tensorVacuum H)))) = _
  rw [ContinuousLinearMap.adjoint_inner_right, secondQuantizationIsometry_vacuum]
  change inner ℂ (secondQuantizationIsometry V (tensorVacuum H)) _ = _
  rw [secondQuantizationIsometry_vacuum]

end FreeProbability.Fock

import FreeProbability.Analytic.TracialL1

/-! # Actual bounded left and right multiplication on complete tracial L1 -/

namespace FreeProbability

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

private theorem tracialL1_precomp_mem (φ : StarProbabilitySpace A) (B : A →L[ℂ] A)
    (F : A → A) (hF : ∀ T, (tracialDualEmbedding φ T).comp B = tracialDualEmbedding φ (F T))
    (x : tracialL1Space φ) : (x : A →L[ℂ] ℂ).comp B ∈ tracialL1Space φ := by
  let L : (A →L[ℂ] ℂ) →L[ℂ] (A →L[ℂ] ℂ) := (ContinuousLinearMap.compL ℂ A A ℂ).flip B
  have hr : ((tracialDualEmbedding φ).range : Set (A →L[ℂ] ℂ)) ⊆
      L ⁻¹' (tracialL1Space φ : Set (A →L[ℂ] ℂ)) := by
    rintro f ⟨T, rfl⟩
    change (tracialDualEmbedding φ T).comp B ∈ tracialL1Space φ
    rw [hF]
    exact (tracialL1Embedding φ (F T)).property
  have hc : IsClosed (L ⁻¹' (tracialL1Space φ : Set (A →L[ℂ] ℂ))) :=
    (tracialDualEmbedding φ).range.isClosed_topologicalClosure.preimage L.continuous
  exact closure_minimal hr hc x.property

private theorem dual_mulLeft_identity (φ : StarProbabilitySpace A) (S T : A) :
    (tracialDualEmbedding φ T).comp ((ContinuousLinearMap.mul ℂ A).flip S) =
      tracialDualEmbedding φ (S * T) := by
  ext U
  exact congrArg φ.expectation (mul_assoc U S T)

private theorem dual_mulRight_identity (φ : StarProbabilitySpace A)
    (hφ : IsTracial φ.toProbabilitySpace) (S T : A) :
    (tracialDualEmbedding φ T).comp (ContinuousLinearMap.mul ℂ A S) =
      tracialDualEmbedding φ (T * S) := by
  ext U
  change φ.expectation ((S * U) * T) = φ.expectation (U * (T * S))
  rw [mul_assoc, hφ S (U * T), mul_assoc]

/-- Genuine left multiplication by a bounded algebra element, on completed L1. -/
noncomputable def tracialL1MulLeft (φ : StarProbabilitySpace A) (S : A) :
    tracialL1Space φ →L[ℂ] tracialL1Space φ :=
  (((ContinuousLinearMap.compL ℂ A A ℂ).flip ((ContinuousLinearMap.mul ℂ A).flip S)).comp
    (tracialL1Space φ).subtypeL).codRestrict (tracialL1Space φ)
      (tracialL1_precomp_mem φ _ (fun T => S * T) (dual_mulLeft_identity φ S))

/-- Genuine right multiplication on completed L1, using the trace identity. -/
noncomputable def tracialL1MulRight (φ : StarProbabilitySpace A)
    (hφ : IsTracial φ.toProbabilitySpace) (S : A) :
    tracialL1Space φ →L[ℂ] tracialL1Space φ :=
  (((ContinuousLinearMap.compL ℂ A A ℂ).flip (ContinuousLinearMap.mul ℂ A S)).comp
    (tracialL1Space φ).subtypeL).codRestrict (tracialL1Space φ)
      (tracialL1_precomp_mem φ _ (fun T => T * S) (dual_mulRight_identity φ hφ S))

@[simp] theorem tracialL1MulLeft_embedding (φ : StarProbabilitySpace A) (S T : A) :
    tracialL1MulLeft φ S (tracialL1Embedding φ T) = tracialL1Embedding φ (S * T) := by
  apply Subtype.ext
  exact dual_mulLeft_identity φ S T

@[simp] theorem tracialL1MulRight_embedding (φ : StarProbabilitySpace A)
    (hφ : IsTracial φ.toProbabilitySpace) (S T : A) :
    tracialL1MulRight φ hφ S (tracialL1Embedding φ T) = tracialL1Embedding φ (T * S) := by
  apply Subtype.ext
  exact dual_mulRight_identity φ hφ S T

theorem tracialL1MulLeft_norm_bound (φ : StarProbabilitySpace A) (S : A) (x : tracialL1Space φ) :
    ‖tracialL1MulLeft φ S x‖ ≤ ‖S‖ * ‖x‖ := by
  change ‖(x : A →L[ℂ] ℂ).comp ((ContinuousLinearMap.mul ℂ A).flip S)‖ ≤ _
  have hb : ‖(ContinuousLinearMap.mul ℂ A).flip S‖ ≤ ‖S‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg S)
    intro U
    exact (norm_mul_le U S).trans_eq (mul_comm _ _)
  exact ((x : A →L[ℂ] ℂ).opNorm_comp_le _).trans
    ((mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans_eq (mul_comm _ _))

theorem tracialL1MulRight_norm_bound (φ : StarProbabilitySpace A)
    (hφ : IsTracial φ.toProbabilitySpace) (S : A) (x : tracialL1Space φ) :
    ‖tracialL1MulRight φ hφ S x‖ ≤ ‖S‖ * ‖x‖ := by
  change ‖(x : A →L[ℂ] ℂ).comp (ContinuousLinearMap.mul ℂ A S)‖ ≤ _
  exact ((x : A →L[ℂ] ℂ).opNorm_comp_le _).trans
    ((mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_mul_apply_le ℂ A S)
      (norm_nonneg _)).trans_eq (mul_comm _ _))

theorem tracialSize_mul_left_le (φ : StarProbabilitySpace A)
    (hφ : IsTracial φ.toProbabilitySpace) (S T : A) :
    tracialSize φ (S * T) ≤ ‖S‖ * tracialSize φ T := by
  simpa only [tracialL1MulLeft_embedding, tracialL1Embedding_norm φ hφ] using
    tracialL1MulLeft_norm_bound φ S (tracialL1Embedding φ T)

theorem tracialSize_mul_right_le (φ : StarProbabilitySpace A)
    (hφ : IsTracial φ.toProbabilitySpace) (S T : A) :
    tracialSize φ (T * S) ≤ ‖S‖ * tracialSize φ T := by
  simpa only [tracialL1MulRight_embedding, tracialL1Embedding_norm φ hφ] using
    tracialL1MulRight_norm_bound φ hφ S (tracialL1Embedding φ T)

@[simp] theorem tracialL1MulLeft_one (φ : StarProbabilitySpace A) (x : tracialL1Space φ) :
    tracialL1MulLeft φ 1 x = x := by
  apply Subtype.ext
  ext U
  change (x : A →L[ℂ] ℂ) (U * 1) = (x : A →L[ℂ] ℂ) U
  rw [mul_one]

@[simp] theorem tracialL1MulRight_one (φ : StarProbabilitySpace A)
    (hφ : IsTracial φ.toProbabilitySpace) (x : tracialL1Space φ) :
    tracialL1MulRight φ hφ 1 x = x := by
  apply Subtype.ext
  ext U
  change (x : A →L[ℂ] ℂ) (1 * U) = (x : A →L[ℂ] ℂ) U
  rw [one_mul]

theorem tracialL1MulLeft_mul (φ : StarProbabilitySpace A) (S T : A) (x : tracialL1Space φ) :
    tracialL1MulLeft φ S (tracialL1MulLeft φ T x) = tracialL1MulLeft φ (S * T) x := by
  apply Subtype.ext
  ext U
  change (x : A →L[ℂ] ℂ) ((U * S) * T) = (x : A →L[ℂ] ℂ) (U * (S * T))
  rw [mul_assoc]

theorem tracialL1MulRight_mul (φ : StarProbabilitySpace A)
    (hφ : IsTracial φ.toProbabilitySpace) (S T : A) (x : tracialL1Space φ) :
    tracialL1MulRight φ hφ T (tracialL1MulRight φ hφ S x) =
      tracialL1MulRight φ hφ (S * T) x := by
  apply Subtype.ext
  ext U
  change (x : A →L[ℂ] ℂ) (S * (T * U)) = (x : A →L[ℂ] ℂ) ((S * T) * U)
  rw [mul_assoc]

theorem tracialL1MulLeft_right_commute (φ : StarProbabilitySpace A)
    (hφ : IsTracial φ.toProbabilitySpace) (S T : A) (x : tracialL1Space φ) :
    tracialL1MulLeft φ S (tracialL1MulRight φ hφ T x) =
      tracialL1MulRight φ hφ T (tracialL1MulLeft φ S x) := by
  apply Subtype.ext
  ext U
  change (x : A →L[ℂ] ℂ) (T * (U * S)) = (x : A →L[ℂ] ℂ) ((T * U) * S)
  rw [mul_assoc]

end FreeProbability

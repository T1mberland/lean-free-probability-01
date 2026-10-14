import FreeProbability.Analytic.TracialDualNormUpper

/-! # The genuine bounded-algebra tracial L1 completion

This complete complex normed space is the norm closure of the actual trace
pairing in the continuous dual. For faithful tracial states the bounded algebra
embeds injectively and densely with norm `τ(|T|)`. No representation by affiliated
operators or identification with a von Neumann predual is asserted.
-/

namespace FreeProbability

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The complete norm closure of the actual trace-dual image. -/
noncomputable def tracialL1Space (φ : StarProbabilitySpace A) :
    Submodule ℂ (A →L[ℂ] ℂ) :=
  (tracialDualEmbedding φ).range.topologicalClosure

noncomputable instance (φ : StarProbabilitySpace A) : CompleteSpace (tracialL1Space φ) := by
  unfold tracialL1Space
  infer_instance

/-- The bounded algebra maps to its genuine L1 completion. -/
noncomputable def tracialL1Embedding (φ : StarProbabilitySpace A) : A →L[ℂ] tracialL1Space φ :=
  (tracialDualEmbedding φ).codRestrict (tracialL1Space φ) fun T =>
    (tracialDualEmbedding φ).range.le_topologicalClosure ⟨T, rfl⟩

@[simp] theorem tracialL1Embedding_coe (φ : StarProbabilitySpace A) (T : A) :
    (tracialL1Embedding φ T : A →L[ℂ] ℂ) = tracialDualEmbedding φ T := rfl

theorem tracialL1Embedding_denseRange (φ : StarProbabilitySpace A) :
    DenseRange (tracialL1Embedding φ) := by
  rw [DenseRange, Subtype.dense_iff, ← Set.range_comp]
  change (tracialL1Space φ : Set (A →L[ℂ] ℂ)) ⊆ closure (Set.range (tracialDualEmbedding φ))
  exact Set.Subset.rfl

theorem tracialL1Embedding_injective (φ : StarProbabilitySpace A)
    (hφ : IsFaithful φ.toProbabilitySpace) : Function.Injective (tracialL1Embedding φ) := by
  intro T U h
  apply tracialDualEmbedding_injective φ hφ
  exact congrArg (fun x : tracialL1Space φ => (x : A →L[ℂ] ℂ)) h

theorem tracialL1Embedding_norm (φ : StarProbabilitySpace A)
    (hφ : IsTracial φ.toProbabilitySpace) (T : A) :
    ‖tracialL1Embedding φ T‖ = tracialSize φ T :=
  tracialDualEmbedding_norm_eq_size φ hφ T

theorem tracialL1Embedding_dist (φ : StarProbabilitySpace A)
    (hφ : IsTracial φ.toProbabilitySpace) (T U : A) :
    dist (tracialL1Embedding φ T) (tracialL1Embedding φ U) = tracialSize φ (T - U) := by
  change dist (tracialDualEmbedding φ T) (tracialDualEmbedding φ U) = _
  rw [dist_eq_norm, ← map_sub]
  exact tracialDualEmbedding_norm_eq_size φ hφ _

/-- Every original bounded test operator acts continuously on completed L1. -/
noncomputable def tracialL1Pairing (φ : StarProbabilitySpace A) (S : A) :
    tracialL1Space φ →L[ℂ] ℂ :=
  (ContinuousLinearMap.apply ℂ ℂ S).comp (tracialL1Space φ).subtypeL

@[simp] theorem tracialL1Pairing_embedding (φ : StarProbabilitySpace A) (S T : A) :
    tracialL1Pairing φ S (tracialL1Embedding φ T) = φ.expectation (S * T) := rfl

theorem tracialL1Pairing_bound (φ : StarProbabilitySpace A) (S : A) (x : tracialL1Space φ) :
    ‖tracialL1Pairing φ S x‖ ≤ ‖S‖ * ‖x‖ := by
  exact ((x : A →L[ℂ] ℂ).le_opNorm S).trans_eq (mul_comm _ _)

/-- The expectation itself extends to the complete space by testing against the unit. -/
noncomputable def tracialL1Expectation (φ : StarProbabilitySpace A) :
    tracialL1Space φ →L[ℂ] ℂ := tracialL1Pairing φ 1

@[simp] theorem tracialL1Expectation_embedding (φ : StarProbabilitySpace A) (T : A) :
    tracialL1Expectation φ (tracialL1Embedding φ T) = φ.expectation T := by
  simp [tracialL1Expectation]

end FreeProbability

import FreeProbability.Analytic.TracialL1

/-! # Trace-symmetric bounded maps on actual completed L1

The extension is genuine dual precomposition restricted to the closed trace
image. Contractivity follows from the actual operator norm of the original map.
-/

namespace FreeProbability

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Bilinear trace symmetry, with the precise ordered product pairing. -/
def IsTracialPairingSymmetric (φ : StarProbabilitySpace A) (P : A →L[ℂ] A) : Prop :=
  ∀ S T, φ.expectation (S * P T) = φ.expectation (P S * T)

private theorem tracialL1Extension_mem (φ : StarProbabilitySpace A) (P : A →L[ℂ] A)
    (hP : IsTracialPairingSymmetric φ P) (x : tracialL1Space φ) :
    (x : A →L[ℂ] ℂ).comp P ∈ tracialL1Space φ := by
  let L : (A →L[ℂ] ℂ) →L[ℂ] (A →L[ℂ] ℂ) := (ContinuousLinearMap.compL ℂ A A ℂ).flip P
  have hr : ((tracialDualEmbedding φ).range : Set (A →L[ℂ] ℂ)) ⊆
      L ⁻¹' (tracialL1Space φ : Set (A →L[ℂ] ℂ)) := by
    rintro f ⟨T, rfl⟩
    have he : (tracialDualEmbedding φ T).comp P = tracialDualEmbedding φ (P T) := by
      ext S
      exact (hP S T).symm
    change (tracialDualEmbedding φ T).comp P ∈ tracialL1Space φ
    rw [he]
    exact (tracialL1Embedding φ (P T)).property
  have hc : IsClosed (L ⁻¹' (tracialL1Space φ : Set (A →L[ℂ] ℂ))) :=
    (tracialDualEmbedding φ).range.isClosed_topologicalClosure.preimage L.continuous
  exact closure_minimal hr hc x.property

/-- The actual complete L1 extension of a trace-symmetric bounded map. -/
noncomputable def tracialL1Extension (φ : StarProbabilitySpace A) (P : A →L[ℂ] A)
    (hP : IsTracialPairingSymmetric φ P) : tracialL1Space φ →L[ℂ] tracialL1Space φ :=
  (((ContinuousLinearMap.compL ℂ A A ℂ).flip P).comp (tracialL1Space φ).subtypeL).codRestrict
    (tracialL1Space φ) (tracialL1Extension_mem φ P hP)

@[simp] theorem tracialL1Extension_embedding (φ : StarProbabilitySpace A) (P : A →L[ℂ] A)
    (hP : IsTracialPairingSymmetric φ P) (T : A) :
    tracialL1Extension φ P hP (tracialL1Embedding φ T) = tracialL1Embedding φ (P T) := by
  apply Subtype.ext
  ext S
  exact (hP S T).symm

theorem tracialL1Extension_norm_bound (φ : StarProbabilitySpace A) (P : A →L[ℂ] A)
    (hP : IsTracialPairingSymmetric φ P) (x : tracialL1Space φ) :
    ‖tracialL1Extension φ P hP x‖ ≤ ‖P‖ * ‖x‖ := by
  change ‖(x : A →L[ℂ] ℂ).comp P‖ ≤ _
  exact ((x : A →L[ℂ] ℂ).opNorm_comp_le P).trans_eq (mul_comm _ _)

theorem tracialL1Extension_contracts (φ : StarProbabilitySpace A) (P : A →L[ℂ] A)
    (hP : IsTracialPairingSymmetric φ P) (hp : ‖P‖ ≤ 1) (x : tracialL1Space φ) :
    ‖tracialL1Extension φ P hP x‖ ≤ ‖x‖ := by
  exact (tracialL1Extension_norm_bound φ P hP x).trans
    ((mul_le_mul_of_nonneg_right hp (norm_nonneg x)).trans_eq (one_mul _))

theorem tracialL1Extension_pairing (φ : StarProbabilitySpace A) (P : A →L[ℂ] A)
    (hP : IsTracialPairingSymmetric φ P) (S : A) (x : tracialL1Space φ) :
    tracialL1Pairing φ S (tracialL1Extension φ P hP x) = tracialL1Pairing φ (P S) x := rfl

theorem tracialL1Extension_expectation (φ : StarProbabilitySpace A) (P : A →L[ℂ] A)
    (hP : IsTracialPairingSymmetric φ P) (h1 : P 1 = 1) (x : tracialL1Space φ) :
    tracialL1Expectation φ (tracialL1Extension φ P hP x) = tracialL1Expectation φ x := by
  change (x : A →L[ℂ] ℂ) (P 1) = (x : A →L[ℂ] ℂ) 1
  rw [h1]

theorem tracialSize_map_le (φ : StarProbabilitySpace A)
    (hφ : IsTracial φ.toProbabilitySpace) (P : A →L[ℂ] A)
    (hP : IsTracialPairingSymmetric φ P) (hp : ‖P‖ ≤ 1) (T : A) :
    tracialSize φ (P T) ≤ tracialSize φ T := by
  simpa only [tracialL1Extension_embedding, tracialL1Embedding_norm φ hφ] using
    tracialL1Extension_contracts φ P hP hp (tracialL1Embedding φ T)

end FreeProbability

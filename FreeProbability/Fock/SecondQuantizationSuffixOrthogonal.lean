import FreeProbability.Fock.SecondQuantizationSuffixTransport

/-! # ALL orthogonal-complement creators commute with actual suffix amplification -/
noncomputable section
open scoped Classical
namespace FreeProbability.Fock
attribute [local irreducible] fullFockTensorDecomposition isometryPrefixTargetUnitary
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

@[simp] theorem isometryPrefixAlphabet_inr (V : H →ₗᵢ[ℂ] K) (j : IsometryPrefixOutside V) :
    isometryPrefixAlphabet V (Sum.inr j) = j.val := rfl

/-- True geometric orthogonal-complement commutation, for every vector and every source bounded operator. -/
theorem isometrySuffixEmbedding_commute_creation_orthogonal (V : H →ₗᵢ[ℂ] K)
    (T : TensorFullFock H →L[ℂ] TensorFullFock H) (k : K)
    (hk : ∀ h : H, inner ℂ (V h) k = 0) :
    Commute (isometrySuffixEmbedding V T) (tensorCreation K k) := by
  let b := (isometryPrefixBasis V).basis
  let S := isometrySuffixEmbedding V T
  let F := (ContinuousLinearMap.mul ℂ (TensorFullFock K →L[ℂ] TensorFullFock K) S).comp
    (prefixTensorCreationContinuous K)
  let G := ((ContinuousLinearMap.mul ℂ (TensorFullFock K →L[ℂ] TensorFullFock K)).flip S).comp
    (prefixTensorCreationContinuous K)
  have hs := F.hasSum (b.hasSum_repr k)
  have ht := G.hasSum (b.hasSum_repr k)
  have heq (j : (isometryPrefixBasis V).indices) : F (b.repr k j • b j) = G (b.repr k j • b j) := by
    by_cases hj : j ∈ Set.range (isometryPrefixBasis V).index
    · obtain ⟨i, rfl⟩ := hj
      have hz : b.repr k ((isometryPrefixBasis V).index i) = 0 := by
        rw [HilbertBasis.repr_apply_apply]
        change inner ℂ ((isometryPrefixBasis V).basis ((isometryPrefixBasis V).index i)) k = 0
        rw [(isometryPrefixBasis V).basis_index]
        exact hk (fullFockBasis H i)
      rw [hz, zero_smul, map_zero, map_zero]
    · rw [map_smul, map_smul]
      apply congrArg (b.repr k j • ·)
      have hc := isometrySuffixEmbedding_commute_creation_outside_basis V T ⟨j, hj⟩
      rw [isometryPrefixAlphabet_inr] at hc
      exact hc.eq
  simp only [heq] at hs
  exact hs.unique ht

/-- The entire geometric orthogonal-complement annihilator family also commutes by genuine adjoints. -/
theorem isometrySuffixEmbedding_commute_annihilation_orthogonal (V : H →ₗᵢ[ℂ] K)
    (T : TensorFullFock H →L[ℂ] TensorFullFock H) (k : K)
    (hk : ∀ h : H, inner ℂ (V h) k = 0) :
    Commute (isometrySuffixEmbedding V T) (tensorAnnihilation K k) := by
  have h := congrArg star (isometrySuffixEmbedding_commute_creation_orthogonal V (star T) k hk).eq
  simp only [star_mul, map_star, star_star] at h
  exact h.symm

end FreeProbability.Fock

import FreeProbability.Fock.WickDampedReconstructionBounds
import FreeProbability.Fock.OrnsteinUhlenbeckFamilyCyclicBasisDamping

/-! # Exact vacuum recovery of the genuine OU-damped full Wick series -/
noncomputable section
open scoped Classical InnerProductSpace
namespace FreeProbability.Fock
variable {I : Type*}

/-- The original word-space OU operator acts by its exact eigenvalue on every complete homogeneous sector. -/
theorem familyWordDegreeDamping_levelEmbedding (t : ℝ) (ht : 0 ≤ t) (n : ℕ) (f : WordLevel I n) :
    familyWordDegreeDamping t ht (levelEmbedding n f) = degreeWeight t n • levelEmbedding n f := by
  have hs := (familyWordDegreeDamping t ht).hasSum (hasSum_levelEmbedding n f)
  have ht' := (hasSum_levelEmbedding n f).const_smul (degreeWeight t n)
  have he (a : Fin n → I) :
      familyWordDegreeDamping t ht (f a • word (List.ofFn a)) =
        degreeWeight t n • (f a • word (List.ofFn a)) := by
    rw [map_smul, familyWordDegreeDamping_word, List.length_ofFn, smul_comm]
  simp only [he] at hs
  exact hs.unique ht'

/-- Every strictly positive OU time gives a genuine convergent reconstruction parameter. -/
theorem norm_ouWickParameter_lt_one (t : ℝ) (ht : 0 < t) :
    ‖(Real.exp (-t) : ℂ)‖ < 1 := by
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht)

/-- Applying the actual full reconstructed operator to the vacuum recovers exactly the completed OU-damped vector. -/
theorem dampedWickReconstruction_ou_vacuum (t : ℝ) (ht : 0 < t) (f : WordSpace I) :
    dampedWickReconstruction (Real.exp (-t) : ℂ) f vacuum =
      familyWordDegreeDamping t ht.le f := by
  have hs := (ContinuousLinearMap.apply ℂ (WordSpace I) vacuum).hasSum
    (hasSum_dampedWickReconstruction_apply (Real.exp (-t) : ℂ)
      (norm_ouWickParameter_lt_one t ht) f)
  simp only [map_smul, ContinuousLinearMap.apply_apply, homogeneousWickCompletion_vacuum] at hs
  have hg := (familyWordDegreeDamping t ht.le).hasSum
    (hasSum_lengthDecomposition_symm (lengthDecomposition f))
  simp only [familyWordDegreeDamping_levelEmbedding, LinearIsometryEquiv.symm_apply_apply] at hg
  exact hs.unique hg

end FreeProbability.Fock

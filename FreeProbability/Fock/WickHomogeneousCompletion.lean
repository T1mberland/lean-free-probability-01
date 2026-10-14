import FreeProbability.Fock.WickHomogeneousCoefficients
import FreeProbability.Fock.ClosedGeneratedState
import Mathlib.Analysis.Normed.Operator.Extend

/-! # Genuine bounded homogeneous Wick reconstruction of arbitrary square-summable coefficients -/
noncomputable section
open scoped Classical InnerProductSpace
namespace FreeProbability.Fock
variable {I : Type*}

/-- The actual continuous extension of finite homogeneous Wick reconstruction to its complete coefficient Hilbert space. -/
def homogeneousWickCompletion (n : ℕ) :
    WordLevel I n →L[ℂ] (WordSpace I →L[ℂ] WordSpace I) :=
  (homogeneousWickLinear n).extendOfNorm (homogeneousCoefficientEmbedding n)

@[simp] theorem homogeneousWickCompletion_coefficientEmbedding (n : ℕ) (c : (Fin n → I) →₀ ℂ) :
    homogeneousWickCompletion n (homogeneousCoefficientEmbedding n c) = homogeneousWick n c := by
  exact LinearMap.extendOfNorm_eq (homogeneousCoefficientEmbedding_denseRange n)
    ⟨(n : ℝ) + 1, norm_homogeneousWickLinear_le n⟩ c

/-- The complete-coefficient Haagerup bound, without finite-support restrictions. -/
theorem norm_homogeneousWickCompletion_apply_le (n : ℕ) (f : WordLevel I n) :
    ‖homogeneousWickCompletion n f‖ ≤ ((n : ℝ) + 1) * ‖f‖ :=
  LinearMap.norm_extendOfNorm_apply_le (homogeneousCoefficientEmbedding_denseRange n)
    ((n : ℝ) + 1) (norm_homogeneousWickLinear_le n) f

/-- The actual completed reconstruction has the same degree-dependent operator bound. -/
theorem norm_homogeneousWickCompletion_le (n : ℕ) :
    ‖homogeneousWickCompletion (I := I) n‖ ≤ (n : ℝ) + 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact norm_homogeneousWickCompletion_apply_le n

/-- Every infinite coefficient vector is recovered exactly by applying its reconstructed Wick operator to the vacuum. -/
theorem homogeneousWickCompletion_vacuum (n : ℕ) (f : WordLevel I n) :
    homogeneousWickCompletion n f (vacuum : WordSpace I) = levelEmbedding n f := by
  have hc : IsClosed {g : WordLevel I n |
      homogeneousWickCompletion n g (vacuum : WordSpace I) = levelEmbedding n g} :=
    isClosed_eq ((homogeneousWickCompletion n).continuous.clm_apply continuous_const)
      (levelEmbedding n).continuous
  have hm (g : WordLevel I n) (hg : g ∈ Set.range (homogeneousCoefficientEmbedding n)) :
      homogeneousWickCompletion n g (vacuum : WordSpace I) = levelEmbedding n g := by
    obtain ⟨c, rfl⟩ := hg
    rw [homogeneousWickCompletion_coefficientEmbedding, homogeneousWick_vacuum_coefficientEmbedding]
  exact (homogeneousCoefficientEmbedding_denseRange n).induction hm hc f

/-- The finite homogeneous operators belong to the actual polynomial algebra. -/
theorem homogeneousWick_mem_algebra (n : ℕ) (c : (Fin n → I) →₀ ℂ) :
    homogeneousWick n c ∈ semicircularAlgebra I := by
  unfold homogeneousWick Finsupp.sum
  apply (semicircularAlgebra I).sum_mem
  intro a _
  exact (semicircularAlgebra I).smul_mem (wick_mem_algebra (List.ofFn a)) (c a)

/-- Arbitrary complete-coefficient reconstruction belongs to the original norm-closed generated algebra. -/
theorem homogeneousWickCompletion_mem_closedAlgebra (n : ℕ) (f : WordLevel I n) :
    homogeneousWickCompletion n f ∈ closedSemicircularAlgebra I := by
  have hc : IsClosed {g : WordLevel I n | homogeneousWickCompletion n g ∈ closedSemicircularAlgebra I} :=
    (semicircularAlgebra I).isClosed_topologicalClosure.preimage (homogeneousWickCompletion n).continuous
  have hm (g : WordLevel I n) (hg : g ∈ Set.range (homogeneousCoefficientEmbedding n)) :
      homogeneousWickCompletion n g ∈ closedSemicircularAlgebra I := by
    obtain ⟨c, rfl⟩ := hg
    rw [homogeneousWickCompletion_coefficientEmbedding]
    exact (semicircularAlgebra I).le_topologicalClosure (homogeneousWick_mem_algebra n c)
  exact (homogeneousCoefficientEmbedding_denseRange n).induction hm hc f

/-- Actual vacuum recovery makes full homogeneous Wick reconstruction injective. -/
theorem homogeneousWickCompletion_injective (n : ℕ) :
    Function.Injective (homogeneousWickCompletion (I := I) n) := by
  intro f g h
  have hv := congrArg (fun T : WordSpace I →L[ℂ] WordSpace I => T vacuum) h
  rw [homogeneousWickCompletion_vacuum, homogeneousWickCompletion_vacuum] at hv
  exact (levelEmbedding n).injective hv
end FreeProbability.Fock

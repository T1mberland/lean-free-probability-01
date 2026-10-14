import FreeProbability.Fock.WickNormHaagerup
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Actual dense finite coefficient vectors and homogeneous Wick linear bounds -/
noncomputable section
open scoped Classical InnerProductSpace ENNReal
namespace FreeProbability.Fock
variable {I : Type*}

/-- The actual finite coefficient vector in the complete fixed-degree Hilbert space. -/
def homogeneousCoefficientEmbedding (n : ℕ) : ((Fin n → I) →₀ ℂ) →ₗ[ℂ] WordLevel I n :=
  Finsupp.linearCombination ℂ (fun a => lp.single 2 a 1)

@[simp] theorem homogeneousCoefficientEmbedding_single (n : ℕ) (a : Fin n → I) (c : ℂ) :
    homogeneousCoefficientEmbedding n (Finsupp.single a c) = lp.single 2 a c := by
  rw [homogeneousCoefficientEmbedding, Finsupp.linearCombination_single, ← lp.single_smul]
  simp only [smul_eq_mul, mul_one]

/-- Finite coefficients are genuinely dense, with no finite/countable alphabet assumption. -/
theorem homogeneousCoefficientEmbedding_denseRange (n : ℕ) :
    DenseRange (homogeneousCoefficientEmbedding (I := I) n) := by
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_forall
  intro f
  have hs (S : Finset (Fin n → I)) :
      (∑ a ∈ S, lp.single 2 a (f a)) ∈ closure (Set.range (homogeneousCoefficientEmbedding n)) := by
    apply subset_closure
    change (∑ a ∈ S, lp.single 2 a (f a)) ∈ LinearMap.range (homogeneousCoefficientEmbedding n)
    apply Submodule.sum_mem
    intro a _
    exact ⟨Finsupp.single a (f a), homogeneousCoefficientEmbedding_single n a (f a)⟩
  exact isClosed_closure.mem_of_tendsto
    (lp.hasSum_single (ENNReal.ofNat_ne_top (n := 2)) f) (Filter.Eventually.of_forall hs)

/-- The genuine vacuum vector of the finite Wick operator is its actual coefficient level embedding. -/
theorem homogeneousWick_vacuum_coefficientEmbedding (n : ℕ) (c : (Fin n → I) →₀ ℂ) :
    homogeneousWick n c (vacuum : WordSpace I) =
      levelEmbedding n (homogeneousCoefficientEmbedding n c) := by
  rw [homogeneousWick_vacuum]
  simp only [homogeneousCoefficientEmbedding, Finsupp.linearCombination_apply, Finsupp.sum,
    map_sum, map_smul, levelEmbedding_single, one_smul]

/-- The finite homogeneous Wick reconstruction is an actual algebraic linear map. -/
def homogeneousWickLinear (n : ℕ) :
    ((Fin n → I) →₀ ℂ) →ₗ[ℂ] (WordSpace I →L[ℂ] WordSpace I) :=
  Finsupp.linearCombination ℂ (fun a => wick (List.ofFn a))

@[simp] theorem homogeneousWickLinear_apply (n : ℕ) (c : (Fin n → I) →₀ ℂ) :
    homogeneousWickLinear n c = homogeneousWick n c := rfl

/-- The original finite Haagerup bound controls reconstruction by the genuine coefficient Hilbert norm. -/
theorem norm_homogeneousWickLinear_le (n : ℕ) (c : (Fin n → I) →₀ ℂ) :
    ‖homogeneousWickLinear n c‖ ≤ ((n : ℝ) + 1) * ‖homogeneousCoefficientEmbedding n c‖ := by
  have h := norm_homogeneousWick_le_degree_mul_vacuumNorm n c
  rw [homogeneousWick_vacuum_coefficientEmbedding, (levelEmbedding n).norm_map] at h
  exact h
end FreeProbability.Fock

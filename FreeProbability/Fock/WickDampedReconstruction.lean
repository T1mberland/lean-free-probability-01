import FreeProbability.Fock.WickHomogeneousCompletion
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Norm-convergent Wick reconstruction from every completed Fock vector -/
noncomputable section
open scoped Classical InnerProductSpace
namespace FreeProbability.Fock
variable {I : Type*}

/-- The actual bounded Wick reconstruction of the nth sector of a full Fock vector. -/
def homogeneousWickSector (n : ℕ) : WordSpace I →L[ℂ] (WordSpace I →L[ℂ] WordSpace I) :=
  (homogeneousWickCompletion n).comp
    ((lp.evalCLM ℂ (fun k => WordLevel I k) 2 n).comp
      lengthDecomposition.toLinearIsometry.toContinuousLinearMap)

@[simp] theorem homogeneousWickSector_apply (n : ℕ) (f : WordSpace I) :
    homogeneousWickSector n f = homogeneousWickCompletion n (lengthDecomposition f n) := rfl

theorem norm_homogeneousWickSector_apply_le (n : ℕ) (f : WordSpace I) :
    ‖homogeneousWickSector n f‖ ≤ ((n : ℝ) + 1) * ‖f‖ := by
  apply (norm_homogeneousWickCompletion_apply_le n _).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (lp.norm_apply_le_norm (by norm_num) (lengthDecomposition f) n).trans_eq
    (lengthDecomposition.norm_map f)

theorem norm_homogeneousWickSector_le (n : ℕ) :
    ‖homogeneousWickSector (I := I) n‖ ≤ (n : ℝ) + 1 :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) (norm_homogeneousWickSector_apply_le n)

theorem summable_wickGeometricBound (z : ℂ) (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * ‖z‖ ^ n) := by
  have h : ‖(‖z‖ : ℝ)‖ < 1 := by simpa using hz
  have hs := (summable_pow_mul_geometric_of_norm_lt_one 1 h).add
    (summable_geometric_of_norm_lt_one h)
  simpa only [pow_one, add_mul, one_mul] using hs

/-- Absolute operator-norm convergence holds for every complex damping parameter in the open unit disk. -/
theorem summable_dampedWickSector (z : ℂ) (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => z ^ n • homogeneousWickSector (I := I) n) := by
  refine Summable.of_norm_bounded (E := WordSpace I →L[ℂ] (WordSpace I →L[ℂ] WordSpace I))
    (summable_wickGeometricBound z hz) ?_
  intro n
  calc
    ‖z ^ n • homogeneousWickSector (I := I) n‖ ≤
        ‖z‖ ^ n * ‖homogeneousWickSector (I := I) n‖ := by
      simpa only [norm_pow] using ContinuousLinearMap.opNorm_smul_le (z ^ n) (homogeneousWickSector (I := I) n)
    _ ≤
        ‖z‖ ^ n * ((n : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (norm_homogeneousWickSector_le n) (by positivity)
    _ = _ := mul_comm _ _

/-- The sum is an actual bounded linear map into bounded operators, rather than a formal Wick series. -/
def dampedWickReconstruction (z : ℂ) : WordSpace I →L[ℂ] (WordSpace I →L[ℂ] WordSpace I) :=
  ∑' n : ℕ, z ^ n • homogeneousWickSector n

theorem hasSum_dampedWickReconstruction (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => z ^ n • homogeneousWickSector (I := I) n)
      (dampedWickReconstruction z) :=
  (summable_dampedWickSector z hz).hasSum

end FreeProbability.Fock

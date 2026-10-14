import FreeProbability.Fock.WickDampedReconstruction

/-! # Quantitative actual Wick series bounds and norm-closed algebra membership -/
noncomputable section
open scoped Classical InnerProductSpace
namespace FreeProbability.Fock
variable {I : Type*}

theorem hasSum_wickGeometricBound (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => ((n : ℝ) + 1) * ‖z‖ ^ n) ((1 - ‖z‖)⁻¹ ^ 2) := by
  have h : ‖(‖z‖ : ℝ)‖ < 1 := by simpa using hz
  have hs := (hasSum_coe_mul_geometric_of_norm_lt_one h).add
    (hasSum_geometric_of_norm_lt_one h)
  have he : ‖z‖ / (1 - ‖z‖) ^ 2 + (1 - ‖z‖)⁻¹ = (1 - ‖z‖)⁻¹ ^ 2 := by
    have hn : 1 - ‖z‖ ≠ 0 := ne_of_gt (sub_pos.mpr hz)
    field_simp
    ring
  simpa only [add_mul, one_mul, he] using hs

/-- A bound independent of the number of generators, valid for every parameter in the open disk. -/
theorem norm_dampedWickReconstruction_le (z : ℂ) (hz : ‖z‖ < 1) :
    ‖dampedWickReconstruction (I := I) z‖ ≤ (1 - ‖z‖)⁻¹ ^ 2 := by
  unfold dampedWickReconstruction
  refine tsum_of_norm_bounded (E := WordSpace I →L[ℂ] (WordSpace I →L[ℂ] WordSpace I))
    (f := fun n : ℕ => z ^ n • homogeneousWickSector (I := I) n)
    (hasSum_wickGeometricBound z hz) ?_
  intro n
  calc
    ‖z ^ n • homogeneousWickSector (I := I) n‖ ≤
        ‖z‖ ^ n * ‖homogeneousWickSector (I := I) n‖ := by
      simpa only [norm_pow] using ContinuousLinearMap.opNorm_smul_le (z ^ n)
        (homogeneousWickSector (I := I) n)
    _ ≤ ‖z‖ ^ n * ((n : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (norm_homogeneousWickSector_le n) (by positivity)
    _ = _ := mul_comm _ _

theorem norm_dampedWickReconstruction_apply_le (z : ℂ) (hz : ‖z‖ < 1) (f : WordSpace I) :
    ‖dampedWickReconstruction z f‖ ≤ (1 - ‖z‖)⁻¹ ^ 2 * ‖f‖ :=
  (dampedWickReconstruction z).le_opNorm f |>.trans
    (mul_le_mul_of_nonneg_right (norm_dampedWickReconstruction_le z hz) (norm_nonneg f))

/-- Applying the genuine bounded reconstruction equals its norm-convergent operator series. -/
theorem hasSum_dampedWickReconstruction_apply (z : ℂ) (hz : ‖z‖ < 1) (f : WordSpace I) :
    HasSum (fun n : ℕ => z ^ n • homogeneousWickCompletion n (lengthDecomposition f n))
      (dampedWickReconstruction z f) := by
  simpa using (ContinuousLinearMap.apply ℂ (WordSpace I →L[ℂ] WordSpace I) f).hasSum
    (hasSum_dampedWickReconstruction z hz)

/-- Every reconstructed full series lies in the original norm-closed generated algebra. -/
theorem dampedWickReconstruction_mem_closedAlgebra (z : ℂ) (hz : ‖z‖ < 1) (f : WordSpace I) :
    dampedWickReconstruction z f ∈ closedSemicircularAlgebra I := by
  apply (semicircularAlgebra I).isClosed_topologicalClosure.mem_of_tendsto
    (hasSum_dampedWickReconstruction_apply z hz f)
  filter_upwards [] with s
  exact (closedSemicircularAlgebra I).sum_mem fun n _ =>
    (closedSemicircularAlgebra I).smul_mem (homogeneousWickCompletion_mem_closedAlgebra n _) (z ^ n)

end FreeProbability.Fock

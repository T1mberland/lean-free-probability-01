import FreeProbability.OperatorValued.MatrixSpectralMaximum

/-! # Positive shifts bounded by the actual upper spectral edge -/
noncomputable section
namespace FreeProbability
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]

omit [PartialOrder A] [StarOrderedRing A] in
theorem realSpectralMaximum_add_norm_nonneg (H : A) (hH : IsSelfAdjoint H) :
    0 ≤ realSpectralMaximum H + ‖H‖ := by
  have hn := spectrum.norm_le_norm_of_mem (realSpectralMaximum_mem H hH)
  have hl : -‖realSpectralMaximum H‖ ≤ realSpectralMaximum H := by
    simpa only [Real.norm_eq_abs] using neg_abs_le (realSpectralMaximum H)
  linarith

/-- This bound uses the upper spectral edge rather than the two-sided operator norm. -/
theorem norm_positiveSpectralShift_le (H : A) (hH : IsSelfAdjoint H) :
    ‖H + algebraMap ℝ A ‖H‖‖ ≤ realSpectralMaximum H + ‖H‖ := by
  have hp : 0 ≤ H + algebraMap ℝ A ‖H‖ := by
    have hh := hH.neg_algebraMap_norm_le_self
    exact neg_le_iff_add_nonneg.mp hh
  apply (CStarAlgebra.norm_le_iff_le_algebraMap _
    (realSpectralMaximum_add_norm_nonneg H hH) hp).mpr
  rw [map_add]
  simpa only [add_comm] using
    add_le_add_right (le_algebraMap_realSpectralMaximum H hH) (algebraMap ℝ A ‖H‖)

end FreeProbability

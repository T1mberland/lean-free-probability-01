import FreeProbability.Analytic.TracialL1Extension
import FreeProbability.Analytic.PositiveMapStar
import FreeProbability.Fock.OrnsteinUhlenbeckVonNeumannVacuumSymmetry
import FreeProbability.Fock.OrnsteinUhlenbeckVonNeumannVacuumSemigroup

/-! # Actual whole-family OU contractions on complete tracial L1 -/

noncomputable section
open scoped CStarAlgebra
namespace FreeProbability.Fock
attribute [local irreducible] fullFockTensorDecomposition isometryPrefixTargetUnitary
  isometrySuffixEmbedding wordSuffixEmbedding doubledRotation secondQuantization isometryPrefixEmbedding
  doubledFockRotation doubledFirst doubledSecond fullFockBasis tensorCreation tensorAnnihilation tensorFamilyField
  tensorFamilyDoubleAlgebra tensorFamilyVonNeumannVacuumState

variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Actual star preservation of the whole double-commutant OU operator. -/
theorem ouVonNeumannTimeCP_map_star (e : I → H) (t : ℝ) (ht : 0 ≤ t)
    (T : tensorFamilyDoubleAlgebra e) :
    ouVonNeumannTimeCP e t ht (star T) = star (ouVonNeumannTimeCP e t ht T) :=
  positiveLinearMap_map_star (PositiveLinearMap.ofClass (ouVonNeumannTimeCP e t ht)) T

/-- The actual sesquilinear vacuum symmetry gives the exact bilinear trace pairing. -/
theorem ouVonNeumannTimeContinuous_pairing_symmetric (e : I → H) (t : ℝ) (ht : 0 ≤ t) :
    IsTracialPairingSymmetric (tensorFamilyVonNeumannVacuumState e)
      (ouVonNeumannTimeContinuous e t ht) := by
  intro S T
  have h := ouVonNeumannTimeCP_state_symmetric e t ht (star S) T
  rw [ouVonNeumannTimeCP_map_star, star_star] at h
  simpa only [star_star, ouVonNeumannTimeContinuous_apply] using h.symm

end FreeProbability.Fock

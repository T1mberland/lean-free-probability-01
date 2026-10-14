import FreeProbability.Fock.OrnsteinUhlenbeckL1Symmetry

/-! # Actual whole-family OU on the complete trace-dual closure

For an orthonormal family the vacuum state is faithful and tracial, so this
complete closure is precisely the bounded-algebra tracial L1 completion.
-/
noncomputable section
namespace FreeProbability.Fock
attribute [local irreducible] fullFockTensorDecomposition isometryPrefixTargetUnitary
  isometrySuffixEmbedding wordSuffixEmbedding doubledRotation secondQuantization isometryPrefixEmbedding
  doubledFockRotation doubledFirst doubledSecond fullFockBasis tensorCreation tensorAnnihilation tensorFamilyField
  tensorFamilyDoubleAlgebra tensorFamilyVonNeumannVacuumState
  ouVonNeumannTimeContinuous tracialL1Space tracialDualEmbedding tracialL1Extension tracialL1Embedding
variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Genuine OU operator on the complete L1 space of the original field double commutant. -/
def ouVonNeumannL1 (e : I → H) (t : ℝ) (ht : 0 ≤ t) :
    tracialL1Space (tensorFamilyVonNeumannVacuumState e) →L[ℂ]
      tracialL1Space (tensorFamilyVonNeumannVacuumState e) :=
  tracialL1Extension (tensorFamilyVonNeumannVacuumState e) (ouVonNeumannTimeContinuous e t ht)
    (ouVonNeumannTimeContinuous_pairing_symmetric e t ht)

@[simp] theorem ouVonNeumannL1_embedding (e : I → H) (t : ℝ) (ht : 0 ≤ t)
    (T : tensorFamilyDoubleAlgebra e) :
    ouVonNeumannL1 e t ht (tracialL1Embedding (tensorFamilyVonNeumannVacuumState e) T) =
      tracialL1Embedding (tensorFamilyVonNeumannVacuumState e)
        (ouVonNeumannTimeContinuous e t ht T) :=
  tracialL1Extension_embedding (tensorFamilyVonNeumannVacuumState e)
    (ouVonNeumannTimeContinuous e t ht) (ouVonNeumannTimeContinuous_pairing_symmetric e t ht) T

end FreeProbability.Fock

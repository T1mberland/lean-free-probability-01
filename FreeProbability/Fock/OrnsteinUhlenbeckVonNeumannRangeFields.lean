import FreeProbability.Fock.OrnsteinUhlenbeckVonNeumannRangeCompression
import FreeProbability.Fock.OrnsteinUhlenbeckDilationGenerators

/-! # Actual suffix images of prescribed-family commutants commute with rotated fields -/
noncomputable section
open scoped Classical InnerProductSpace
namespace FreeProbability.Fock
attribute [local irreducible] fullFockTensorDecomposition isometryPrefixTargetUnitary
  isometrySuffixEmbedding wordSuffixEmbedding
section General
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The field map respects REAL coefficients, using the actual adjoint's conjugate scalars. -/
theorem ouRange_field_real_combination (r s : ℝ) (h k : K) :
    tensorCreation K ((r : ℂ) • h + (s : ℂ) • k) +
      tensorAnnihilation K ((r : ℂ) • h + (s : ℂ) • k) =
      (r : ℂ) • (tensorCreation K h + tensorAnnihilation K h) +
        (s : ℂ) • (tensorCreation K k + tensorAnnihilation K k) := by
  have hc : tensorCreation K ((r : ℂ) • h + (s : ℂ) • k) =
      (r : ℂ) • tensorCreation K h + (s : ℂ) • tensorCreation K k := by
    rw [ou_tensorCreation_add, ou_tensorCreation_smul, ou_tensorCreation_smul]
  have ha := congrArg ContinuousLinearMap.adjoint hc
  rw [map_add, map_smulₛₗ, map_smulₛₗ] at ha
  have hr : starRingEnd ℂ (r : ℂ) = (r : ℂ) := Complex.conj_ofReal r
  have hs : starRingEnd ℂ (s : ℂ) = (s : ℂ) := Complex.conj_ofReal s
  rw [hr, hs] at ha
  change tensorCreation K ((r : ℂ) • h + (s : ℂ) • k) +
    (tensorCreation K ((r : ℂ) • h + (s : ℂ) • k)).adjoint = _
  rw [ha, hc]
  change (r : ℂ) • tensorCreation K h + (s : ℂ) • tensorCreation K k +
    ((r : ℂ) • tensorAnnihilation K h + (s : ℂ) • tensorAnnihilation K k) = _
  module
end General

variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Exact rotated doubled real-field decomposition, on actual complete tensor Fock space. -/
theorem ouRange_rotated_field (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1) (e : I → H) (i : I) :
    tensorFamilyField (fun j => doubledRotation r s hrs (doubledFirst H (e j))) i =
      (r : ℂ) • tensorFamilyField (fun j => doubledFirst H (e j)) i +
        (s : ℂ) • tensorFamilyField (fun j => doubledSecond H (e j)) i := by
  change tensorCreation (DoubledHilbert H) (doubledRotation r s hrs (doubledFirst H (e i))) +
    tensorAnnihilation (DoubledHilbert H) (doubledRotation r s hrs (doubledFirst H (e i))) = _
  rw [doubledRotation_first]
  exact ouRange_field_real_combination r s (doubledFirst H (e i)) (doubledSecond H (e i))

/-- Commutation with a SINGLE prescribed source field implies commutation with its actual rotated doubled field. -/
theorem suffixFirst_commute_rotated_field (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1)
    (e : I → H) (B : TensorFullFock H →L[ℂ] TensorFullFock H) (i : I)
    (hB : Commute B (tensorFamilyField e i)) :
    Commute (isometrySuffixEmbedding (doubledFirst H) B)
      (tensorFamilyField (fun j => doubledRotation r s hrs (doubledFirst H (e j))) i) := by
  have hFirst := isometrySuffixEmbedding_commute_family_field (doubledFirst H) e B i hB
  have hOrth : ∀ h : H, inner ℂ (doubledFirst H h) (doubledSecond H (e i)) = 0 := by
    intro h
    simp [doubledFirst, doubledSecond, WithLp.prod_inner_apply]
  have hc := isometrySuffixEmbedding_commute_creation_orthogonal (doubledFirst H) B
    (doubledSecond H (e i)) hOrth
  have ha := isometrySuffixEmbedding_commute_annihilation_orthogonal (doubledFirst H) B
    (doubledSecond H (e i)) hOrth
  have hSecond : Commute (isometrySuffixEmbedding (doubledFirst H) B)
      (tensorFamilyField (fun j => doubledSecond H (e j)) i) := by
    change isometrySuffixEmbedding (doubledFirst H) B *
      (tensorCreation (DoubledHilbert H) (doubledSecond H (e i)) +
        tensorAnnihilation (DoubledHilbert H) (doubledSecond H (e i))) =
      (tensorCreation (DoubledHilbert H) (doubledSecond H (e i)) +
        tensorAnnihilation (DoubledHilbert H) (doubledSecond H (e i))) *
          isometrySuffixEmbedding (doubledFirst H) B
    rw [mul_add, add_mul, hc.eq, ha.eq]
  change _ * _ = _ * _
  rw [ouRange_rotated_field, mul_add, add_mul, mul_smul_comm, mul_smul_comm,
    smul_mul_assoc, smul_mul_assoc, hFirst.eq, hSecond.eq]

end FreeProbability.Fock

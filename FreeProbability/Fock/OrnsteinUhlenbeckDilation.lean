import FreeProbability.Fock.OrnsteinUhlenbeckRotation

/-!
# Actual rotated Fock compression

A genuine doubled-space rotation is second-quantized and followed by the genuine
unital completely positive Fock inclusion compression. The domain here is the
full doubled bounded-operator algebra; generated-algebra range and the OU
semigroup are separate mathematical obligations.
-/
noncomputable section
open scoped Classical InnerProductSpace CStarAlgebra

namespace FreeProbability.Fock
variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual vacuum-preserving Fock inclusion into doubled complete tensor Fock space. -/
def doubledFockInclusion : TensorFullFock H →ₗᵢ[ℂ] TensorFullFock (DoubledHilbert H) :=
  secondQuantizationIsometry (doubledFirst H)

/-- The actual full doubled-Fock unitary implementing a real rotation. -/
def doubledFockRotation (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1) :
    TensorFullFock (DoubledHilbert H) ≃ₗᵢ[ℂ] TensorFullFock (DoubledHilbert H) :=
  secondQuantization (doubledRotation r s hrs)

@[simp] theorem doubledFockInclusion_vacuum :
    doubledFockInclusion H (tensorVacuum H) = tensorVacuum (DoubledHilbert H) :=
  secondQuantizationIsometry_vacuum _

@[simp] theorem doubledFockRotation_vacuum (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1) :
    doubledFockRotation H r s hrs (tensorVacuum (DoubledHilbert H)) =
      tensorVacuum (DoubledHilbert H) := secondQuantization_vacuum _

/-- Actual rotated compression, bundled with full canonical finite-matrix positivity. -/
def rotatedFockCompression (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1) :
    (TensorFullFock (DoubledHilbert H) →L[ℂ] TensorFullFock (DoubledHilbert H)) →CP
      (TensorFullFock H →L[ℂ] TensorFullFock H) where
  toLinearMap := (secondQuantizationCompression (doubledFirst H)).comp
    (doubledFockRotation H r s hrs).conjStarAlgEquiv.toAlgEquiv.toLinearMap
  map_cstarMatrix_nonneg' _k M hM := by
    let R := (doubledFockRotation H r s hrs).conjStarAlgEquiv
    have hR : 0 ≤ M.map R :=
      map_nonneg (CStarMatrix.mapₙₐ R.toNonUnitalStarAlgHom) hM
    have hC := secondQuantizationCompression_matrix_nonneg (doubledFirst H) (M.map R) hR
    exact hC

/-- The precise operator expression: Γ(inclusion)† Γ(rotation) T Γ(rotation)† Γ(inclusion). -/
theorem rotatedFockCompression_apply (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1)
    (T : TensorFullFock (DoubledHilbert H) →L[ℂ] TensorFullFock (DoubledHilbert H)) :
    rotatedFockCompression H r s hrs T =
      secondQuantizationCompression (doubledFirst H)
        ((doubledFockRotation H r s hrs).conjStarAlgEquiv T) := rfl

@[simp] theorem rotatedFockCompression_one (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1) :
    rotatedFockCompression H r s hrs 1 = 1 := by
  rw [rotatedFockCompression_apply, map_one, secondQuantizationCompression_one]

/-- Actual norm contraction on the whole doubled bounded-operator algebra. -/
theorem norm_rotatedFockCompression_le (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1)
    (T : TensorFullFock (DoubledHilbert H) →L[ℂ] TensorFullFock (DoubledHilbert H)) :
    ‖rotatedFockCompression H r s hrs T‖ ≤ ‖T‖ := by
  rw [rotatedFockCompression_apply]
  have hi : ‖(doubledFockRotation H r s hrs).conjStarAlgEquiv T‖ = ‖T‖ :=
    StarAlgEquiv.norm_map (doubledFockRotation H r s hrs).conjStarAlgEquiv T
  exact (norm_secondQuantizationCompression_le _ _).trans hi.le

/-- Genuine vacuum expectation preservation after the rotation and compression. -/
theorem rotatedFockCompression_vacuum_expectation (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1)
    (T : TensorFullFock (DoubledHilbert H) →L[ℂ] TensorFullFock (DoubledHilbert H)) :
    inner ℂ (tensorVacuum H) (rotatedFockCompression H r s hrs T (tensorVacuum H)) =
      inner ℂ (tensorVacuum (DoubledHilbert H)) (T (tensorVacuum (DoubledHilbert H))) := by
  rw [rotatedFockCompression_apply, secondQuantizationCompression_vacuum_expectation]
  exact secondQuantization_vacuum_expectation _ _

end FreeProbability.Fock

import FreeProbability.Fock.OrnsteinUhlenbeckDilationProjection

/-! # Actual degree-one scaling under the real rotation dilation -/
noncomputable section
open scoped Classical InnerProductSpace CStarAlgebra
namespace FreeProbability.Fock
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Creation is complex linear in its original one-particle Hilbert-space vector. -/
theorem ou_tensorCreation_add (h k : K) : tensorCreation K (h + k) = tensorCreation K h + tensorCreation K k := by
  have hr := (fullFockBasis K).repr.map_add h k
  have hv := vectorCreation_add ((fullFockBasis K).repr h) ((fullFockBasis K).repr k)
  exact (congrArg (fun z => tensorOperatorEquiv K (vectorCreation z)) hr).trans
    ((congrArg (tensorOperatorEquiv K) hv).trans ((tensorOperatorEquiv K).map_add _ _))

theorem ou_tensorCreation_smul (c : ℂ) (h : K) : tensorCreation K (c • h) = c • tensorCreation K h := by
  have hr := (fullFockBasis K).repr.map_smul c h
  have hv := vectorCreation_smul c ((fullFockBasis K).repr h)
  exact (congrArg (fun z => tensorOperatorEquiv K (vectorCreation z)) hr).trans
    ((congrArg (tensorOperatorEquiv K) hv).trans (map_smul (tensorOperatorEquiv K).toAlgEquiv.toAlgHom c _))

/-- The actual compression preserves adjoints, without an algebra-multiplicativity assumption. -/
theorem inclusion_compression_star (V : H →ₗᵢ[ℂ] K)
    (T : TensorFullFock K →L[ℂ] TensorFullFock K) :
    secondQuantizationCompression V (star T) = star (secondQuantizationCompression V T) := by
  change (secondQuantizationIsometry V).toContinuousLinearMap.adjoint.comp
    (T.adjoint.comp (secondQuantizationIsometry V).toContinuousLinearMap) =
      ((secondQuantizationIsometry V).toContinuousLinearMap.adjoint.comp
        (T.comp (secondQuantizationIsometry V).toContinuousLinearMap)).adjoint
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_assoc]

/-- The exact first-degree creator coefficient is the real rotation parameter r. -/
theorem rotatedFockCompression_creation_first (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1) (h : H) :
    rotatedFockCompression H r s hrs (tensorCreation (DoubledHilbert H) (doubledFirst H h)) =
      (r : ℂ) • tensorCreation H h := by
  rw [rotatedFockCompression_apply]
  change secondQuantizationCompression (doubledFirst H)
    ((secondQuantization (doubledRotation r s hrs)).conjStarAlgEquiv
      (tensorCreation (DoubledHilbert H) (doubledFirst H h))) = _
  rw [secondQuantization_conj_creation, doubledRotation_first, ou_tensorCreation_add,
    ou_tensorCreation_smul, ou_tensorCreation_smul, map_add, map_smul, map_smul,
    inclusion_compression_creation, orthogonal_compression_creation _ _ (doubled_noise_orthogonal h)]
  have hz : (s : ℂ) • (0 : TensorFullFock H →L[ℂ] TensorFullFock H) = 0 := by
    apply ContinuousLinearMap.ext
    intro f
    simp
  exact (congrArg ((r : ℂ) • tensorCreation H h + ·) hz).trans (add_zero _)


/-- Real rotation coefficients commute with adjoints; annihilation has the same degree-one factor. -/
theorem rotatedFockCompression_annihilation_first (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1) (h : H) :
    rotatedFockCompression H r s hrs (tensorAnnihilation (DoubledHilbert H) (doubledFirst H h)) =
      (r : ℂ) • tensorAnnihilation H h := by
  have hs : rotatedFockCompression H r s hrs
      (star (tensorCreation (DoubledHilbert H) (doubledFirst H h))) =
      star (rotatedFockCompression H r s hrs
        (tensorCreation (DoubledHilbert H) (doubledFirst H h))) := by
    rw [rotatedFockCompression_apply, map_star, inclusion_compression_star]
    rfl
  change rotatedFockCompression H r s hrs
    (star (tensorCreation (DoubledHilbert H) (doubledFirst H h))) =
      (r : ℂ) • star (tensorCreation H h)
  rw [hs, rotatedFockCompression_creation_first, star_smul, Complex.star_def, Complex.conj_ofReal]

/-- Actual semicircular field scaling, not merely a vacuum or moment identity. -/
theorem rotatedFockCompression_field_first (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1) (h : H) :
    rotatedFockCompression H r s hrs
      (tensorCreation (DoubledHilbert H) (doubledFirst H h) +
        tensorAnnihilation (DoubledHilbert H) (doubledFirst H h)) =
      (r : ℂ) • (tensorCreation H h + tensorAnnihilation H h) := by
  rw [map_add, rotatedFockCompression_creation_first, rotatedFockCompression_annihilation_first,
    smul_add]

/-- At nonnegative time the actual degree-one scaling coefficient is e⁻ᵗ. -/
theorem ouTimeDilation_field_first (t : ℝ) (ht : 0 ≤ t) (h : H) :
    ouTimeDilation H t ht
      (tensorCreation (DoubledHilbert H) (doubledFirst H h) +
        tensorAnnihilation (DoubledHilbert H) (doubledFirst H h)) =
      (Real.exp (-t) : ℂ) • (tensorCreation H h + tensorAnnihilation H h) :=
  rotatedFockCompression_field_first _ _ _ h

end FreeProbability.Fock

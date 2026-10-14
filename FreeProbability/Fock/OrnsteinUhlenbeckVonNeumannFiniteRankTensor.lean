import FreeProbability.Fock.OrnsteinUhlenbeckVonNeumannFiniteRankApproximation
import FreeProbability.Fock.SecondQuantizationWOTCompression
import Mathlib.Analysis.CStarAlgebra.Hom

/-! Actual finite-word approximations transported to the recursively completed tensor Fock space. -/
noncomputable section
open scoped InnerProductSpace Topology
open Filter
namespace FreeProbability.Fock
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Finite-word orthogonal projection on the literal completed tensor-power sum. -/
def finiteTensorWordProjection (S : Finset (List (fullFockBasisSet H))) :
    TensorFullFock H →L[ℂ] TensorFullFock H :=
  (fullFockTensorDecomposition H).conjStarAlgEquiv (finiteWordProjection S)

@[simp] theorem finiteTensorWordProjection_adjoint (S : Finset (List (fullFockBasisSet H))) :
    (finiteTensorWordProjection S).adjoint = finiteTensorWordProjection S := by
  change star ((fullFockTensorDecomposition H).conjStarAlgEquiv (finiteWordProjection S)) = _
  rw [← map_star]
  exact congrArg (fullFockTensorDecomposition H).conjStarAlgEquiv
    (finiteWordProjection_adjoint S)

 theorem norm_finiteTensorWordProjection_le (S : Finset (List (fullFockBasisSet H))) :
    ‖finiteTensorWordProjection S‖ ≤ 1 := by
  unfold finiteTensorWordProjection
  rw [NonUnitalStarAlgHom.norm_map (fullFockTensorDecomposition H).conjStarAlgEquiv
    (fullFockTensorDecomposition H).conjStarAlgEquiv.injective]
  exact norm_finiteWordProjection_le S

/-- The actual tensor operator corresponding to a finite-rank word sandwich. -/
def finiteTensorWordSandwich (S : Finset (List (fullFockBasisSet H)))
    (T : TensorFullFock H →L[ℂ] TensorFullFock H) :
    TensorFullFock H →L[ℂ] TensorFullFock H :=
  (fullFockTensorDecomposition H).conjStarAlgEquiv
    (finiteWordSandwich S ((fullFockTensorDecomposition H).conjStarAlgEquiv.symm T))

theorem finiteTensorWordSandwich_eq_comp (S : Finset (List (fullFockBasisSet H)))
    (T : TensorFullFock H →L[ℂ] TensorFullFock H) :
    finiteTensorWordSandwich S T =
      (finiteTensorWordProjection S).comp (T.comp (finiteTensorWordProjection S)) := by
  change (fullFockTensorDecomposition H).conjStarAlgEquiv
    (finiteWordProjection S *
      ((fullFockTensorDecomposition H).conjStarAlgEquiv.symm T * finiteWordProjection S)) = _
  rw [map_mul, map_mul, StarAlgEquiv.apply_symm_apply]
  rfl

/-- The tensor sandwich has range in a genuinely finite-dimensional transported word span. -/
theorem finiteTensorWordSandwich_mem_span (S : Finset (List (fullFockBasisSet H)))
    (T : TensorFullFock H →L[ℂ] TensorFullFock H) (f : TensorFullFock H) :
    finiteTensorWordSandwich S T f ∈ Submodule.span ℂ
      ((fun w => fullFockTensorDecomposition H (word w)) '' (S : Set _)) := by
  let U := fullFockTensorDecomposition H
  let M := Submodule.span ℂ ((fun w => U (word w)) '' (S : Set _))
  have hmap : Submodule.span ℂ (word '' (S : Set _)) ≤ M.comap U.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro g ⟨w, hw, rfl⟩
    exact Submodule.subset_span ⟨w, hw, rfl⟩
  exact hmap (finiteWordSandwich_mem_span S (U.conjStarAlgEquiv.symm T) (U.symm f))

 theorem finiteTensorWordSandwich_finite_span (S : Finset (List (fullFockBasisSet H))) :
    FiniteDimensional ℂ (Submodule.span ℂ
      ((fun w => fullFockTensorDecomposition H (word w)) '' (S : Set _))) :=
  FiniteDimensional.span_of_finite ℂ (S.finite_toSet.image _)

 theorem finiteTensorWordProjection_tendsto (f : TensorFullFock H) :
    Tendsto (fun S : Finset (List (fullFockBasisSet H)) => finiteTensorWordProjection S f)
      atTop (𝓝 f) := by
  simpa [finiteTensorWordProjection, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    Function.comp_def] using
    ((fullFockTensorDecomposition H).continuous.tendsto
      ((fullFockTensorDecomposition H).symm f)).comp
      (finiteWordProjection_tendsto ((fullFockTensorDecomposition H).symm f))

 theorem norm_finiteTensorWordSandwich_le (S : Finset (List (fullFockBasisSet H)))
    (T : TensorFullFock H →L[ℂ] TensorFullFock H) :
    ‖finiteTensorWordSandwich S T‖ ≤ ‖T‖ := by
  unfold finiteTensorWordSandwich
  rw [NonUnitalStarAlgHom.norm_map (fullFockTensorDecomposition H).conjStarAlgEquiv
    (fullFockTensorDecomposition H).conjStarAlgEquiv.injective]
  exact (norm_finiteWordSandwich_le S _).trans_eq
    (NonUnitalStarAlgHom.norm_map (fullFockTensorDecomposition H).conjStarAlgEquiv.symm
      (fullFockTensorDecomposition H).conjStarAlgEquiv.symm.injective T)

 theorem finiteTensorWordSandwich_tendsto_WOT
    (T : TensorFullFock H →L[ℂ] TensorFullFock H) :
    Tendsto (fun S : Finset (List (fullFockBasisSet H)) =>
      ContinuousLinearMapWOT.ofCLM (finiteTensorWordSandwich S T)) atTop
      (𝓝 (ContinuousLinearMapWOT.ofCLM T)) := by
  have h := (unitaryConjugationWOT_continuous (fullFockTensorDecomposition H)).tendsto
    (ContinuousLinearMapWOT.ofCLM ((fullFockTensorDecomposition H).conjStarAlgEquiv.symm T))
  simpa only [unitaryConjugationWOT, ContinuousLinearMapWOT.toCLM_ofCLM,
    StarAlgEquiv.apply_symm_apply, Function.comp_def, finiteTensorWordSandwich] using
    h.comp (finiteWordSandwich_tendsto_WOT
      ((fullFockTensorDecomposition H).conjStarAlgEquiv.symm T))

end FreeProbability.Fock

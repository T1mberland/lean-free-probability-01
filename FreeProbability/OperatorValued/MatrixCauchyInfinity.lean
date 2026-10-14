import FreeProbability.OperatorValued.MatrixCauchyAnalytic

/-! # Actual resolvent and matrix Cauchy normalization at infinity -/

noncomputable section
open scoped Classical Topology Matrix.Norms.Elementwise
namespace FreeProbability

/-- Normalization of the true Banach-algebra resolvent at infinity, including
algebras whose unit norm need not be one. -/
theorem resolvent_smul_tendsto_one {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] (a : A) :
    Filter.Tendsto (fun z : ℂ => z • resolvent a z) (Bornology.cobounded ℂ) (𝓝 (1 : A)) := by
  have hr := spectrum.resolvent_tendsto_cobounded (𝕜 := ℂ) a
  have ht : Filter.Tendsto (fun z : ℂ => 1 + a * resolvent a z) (Bornology.cobounded ℂ) (𝓝 (1 : A)) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hr)
  have heq : (fun z : ℂ => z • resolvent a z) =ᶠ[Bornology.cobounded ℂ]
      (fun z : ℂ => 1 + a * resolvent a z) := by
    filter_upwards [spectrum.eventually_isUnit_resolvent (𝕜 := ℂ) a] with z hz
    have hx := Ring.mul_inverse_cancel _ (spectrum.isUnit_resolvent.mpr hz)
    change (algebraMap ℂ A z - a) * resolvent a z = 1 at hx
    simp only [sub_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] at hx
    exact sub_eq_iff_eq_add.mp hx
  exact ht.congr' heq.symm

namespace Fock
variable {I n : Type*} [Fintype I] [Fintype n] [DecidableEq n]
local instance : PartialOrder (WordSpace I →L[ℂ] WordSpace I) := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing (WordSpace I →L[ℂ] WordSpace I) :=
  CStarAlgebra.spectralOrderedRing _

/-- The actual affine matrix Cauchy transform has its physical normalization
`z m(z) → I` at infinity, without Hermitian or commutation assumptions. -/
theorem operatorMatrixPencilCauchy_smul_tendsto_one (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ) :
    Filter.Tendsto (fun z : ℂ => z • operatorMatrixPencilCauchy C₀ C z)
      (Bornology.cobounded ℂ) (𝓝 (1 : Matrix n n ℂ)) := by
  have h := matrixVacuumContinuousExpectation.continuous.tendsto
      (1 : CStarMatrix n n (WordSpace I →L[ℂ] WordSpace I)) |>.comp
    (resolvent_smul_tendsto_one (operatorMatrixPencil C₀ C))
  have hunit : matrixVacuumContinuousExpectation
      (1 : CStarMatrix n n (WordSpace I →L[ℂ] WordSpace I)) = (1 : Matrix n n ℂ) := by
    rw [matrixVacuumContinuousExpectation_apply]
    change matrixExpectation (vacuumState I).toProbabilitySpace
      (1 : Matrix n n (WordSpace I →L[ℂ] WordSpace I)) = 1
    simpa using matrixExpectation_scalarMatrixEmbedding (vacuumState I).toProbabilitySpace
      (1 : Matrix n n ℂ)
  have heq : (fun z : ℂ => matrixVacuumContinuousExpectation
      (z • resolvent (operatorMatrixPencil C₀ C) z)) =
      (fun z : ℂ => z • operatorMatrixPencilCauchy C₀ C z) := by
    funext z
    rw [map_smul, matrixVacuumContinuousExpectation_apply]
    rfl
  simpa only [Function.comp_def, heq, hunit] using! h

end Fock
end FreeProbability

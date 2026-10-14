import FreeProbability.Analytic.Expectation
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# The actual positive functional inducing a self-adjoint spectral measure

Pull back the real part of the given positive normalized state through the
continuous functional calculus. This construction needs neither traciality nor
faithfulness; support identification will use faithfulness separately.
-/

noncomputable section
open scoped ComplexOrder CompactlySupported

namespace FreeProbability

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (φ : StarProbabilitySpace A) {a : A} (ha : IsSelfAdjoint a)

/-- The positive real functional on the actual compact real spectrum of a self-adjoint element. -/
def spectralContinuousFunctional : C(spectrum ℝ a, ℝ) →ₚ[ℝ] ℝ where
  toLinearMap := Complex.reLm.comp ((φ.expectation.restrictScalars ℝ).comp
    (cfcHom ha).toAlgHom.toLinearMap)
  monotone' := by
    intro f g hfg
    exact (φ.toPositiveLinearMap.monotone (cfcHom_mono ha hfg)).1

@[simp] theorem spectralContinuousFunctional_apply (f : C(spectrum ℝ a, ℝ)) :
    spectralContinuousFunctional φ ha f = (φ.expectation (cfcHom ha f)).re := rfl

@[simp] theorem spectralContinuousFunctional_one : spectralContinuousFunctional φ ha 1 = 1 := by
  change (φ.expectation (cfcHom ha 1)).re = 1
  rw [map_one, φ.map_one]
  rfl

/-- The compactly supported positive functional used by the actual Riesz representation theorem. -/
def spectralRieszFunctional : C_c(spectrum ℝ a, ℝ) →ₚ[ℝ] ℝ where
  toFun f := spectralContinuousFunctional φ ha f.toContinuousMap
  map_add' f g := by
    change spectralContinuousFunctional φ ha (f.toContinuousMap + g.toContinuousMap) = _
    exact map_add _ _ _
  map_smul' c f := by
    change spectralContinuousFunctional φ ha (c • f.toContinuousMap) = _
    exact map_smul _ _ _
  monotone' := by
    intro f g hfg
    exact (spectralContinuousFunctional φ ha).monotone hfg

end FreeProbability

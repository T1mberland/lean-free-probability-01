import FreeProbability.Fock.OrnsteinUhlenbeckVonNeumannFiniteRankProjection
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology

/-! Uniformly bounded finite-word approximations to every bounded Fock operator.
The directed index consists of all finite sets of words, without enumerating the alphabet. -/
noncomputable section
open scoped InnerProductSpace ENNReal Topology
open Filter
namespace FreeProbability.Fock
variable {I : Type*}

 theorem finiteWordProjection_tendsto (f : WordSpace I) :
    Tendsto (fun S : Finset (List I) => finiteWordProjection S f) atTop (𝓝 f) := by
  classical
  simpa only [HasSum, SummationFilter.unconditional, finiteWordProjection_eq_sum] using
    (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) f)

/-- Sandwich an arbitrary bounded operator by a finite-word orthogonal projection. -/
def finiteWordSandwich (S : Finset (List I)) (T : WordSpace I →L[ℂ] WordSpace I) :
    WordSpace I →L[ℂ] WordSpace I :=
  (finiteWordProjection S).comp (T.comp (finiteWordProjection S))

/-- The sandwiches have range in the same finite-dimensional word span. -/
theorem finiteWordSandwich_mem_span (S : Finset (List I))
    (T : WordSpace I →L[ℂ] WordSpace I) (f : WordSpace I) :
    finiteWordSandwich S T f ∈ Submodule.span ℂ (word '' (S : Set (List I))) :=
  finiteWordProjection_mem_span S (T (finiteWordProjection S f))

 theorem norm_finiteWordSandwich_le (S : Finset (List I))
    (T : WordSpace I →L[ℂ] WordSpace I) : ‖finiteWordSandwich S T‖ ≤ ‖T‖ := by
  calc
    ‖finiteWordSandwich S T‖ ≤ ‖finiteWordProjection S‖ *
        (‖T‖ * ‖finiteWordProjection S‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖T‖ * 1) := by
      gcongr <;> exact norm_finiteWordProjection_le S
    _ = ‖T‖ := by ring

 theorem finiteWordSandwich_coefficient (S : Finset (List I))
    (T : WordSpace I →L[ℂ] WordSpace I) (x y : WordSpace I) :
    inner ℂ y (finiteWordSandwich S T x) =
      inner ℂ (finiteWordProjection S y) (T (finiteWordProjection S x)) := by
  have h := (finiteWordProjection S).adjoint_inner_right y (T (finiteWordProjection S x))
  simpa only [finiteWordProjection_adjoint, finiteWordSandwich, ContinuousLinearMap.comp_apply]
    using h

/-- Every bounded operator is a WOT limit of uniformly bounded, finite-rank sandwiches. -/
 theorem finiteWordSandwich_tendsto_WOT (T : WordSpace I →L[ℂ] WordSpace I) :
    Tendsto (fun S : Finset (List I) =>
      ContinuousLinearMapWOT.ofCLM (finiteWordSandwich S T)) atTop
      (𝓝 (ContinuousLinearMapWOT.ofCLM T)) := by
  apply ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.2
  intro x y
  simpa only [ContinuousLinearMapWOT.ofCLM_apply, finiteWordSandwich_coefficient, Function.comp_apply] using
    (finiteWordProjection_tendsto y).inner
      ((T.continuous.tendsto x).comp (finiteWordProjection_tendsto x))

end FreeProbability.Fock

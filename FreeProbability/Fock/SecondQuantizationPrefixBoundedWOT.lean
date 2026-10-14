import FreeProbability.Fock.SecondQuantizationPrefixOperators
import FreeProbability.Fock.SecondQuantizationWOTCompression
import FreeProbability.Fock.OrnsteinUhlenbeckContinuityDense

/-! # Bounded-WOT continuity of actual infinite Hilbert amplification

The bound is on the source operators. Global WOT continuity on arbitrary
unbounded families is neither assumed nor asserted.
-/
noncomputable section
open scoped Classical InnerProductSpace NNReal ENNReal
namespace FreeProbability.Fock
variable {A E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Source norm ball, carrying the induced genuine WOT topology. -/
abbrev WOTNormBall (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (C : ℝ≥0) := {T : E →WOT[ℂ] E // ‖T.toCLM‖ ≤ C}

def amplificationCoefficientFamily (C : ℝ≥0) (y : ConstantHilbertSum A E) :
    WOTNormBall E C → ConstantHilbertSum A E →L[ℂ] ℂ :=
  fun T => (innerSL ℂ y).comp (hilbertAmplification T.val.toCLM)

theorem amplificationCoefficient_continuous_single (C : ℝ≥0) (y : ConstantHilbertSum A E)
    (a : A) (x : E) :
    Continuous (fun T : WOTNormBall E C => amplificationCoefficientFamily C y T (lp.single 2 a x)) := by
  have heq : (fun T : WOTNormBall E C => amplificationCoefficientFamily C y T (lp.single 2 a x)) =
      (fun T : WOTNormBall E C => inner ℂ (y a) (T.val x)) := by
    funext T
    change inner ℂ y (hilbertAmplification T.val.toCLM (lp.single 2 a x)) = _
    rw [hilbertAmplification_single, lp.inner_single_right]
    rfl
  rw [heq]
  exact (ContinuousLinearMapWOT.continuous_inner_apply continuous_subtype_val x (y a))

theorem amplificationCoefficient_continuous_dense (C : ℝ≥0) (y : ConstantHilbertSum A E) :
    Dense ((continuousOrbitSubmodule (amplificationCoefficientFamily C y)) : Set (ConstantHilbertSum A E)) := by
  let S := continuousOrbitSubmodule (amplificationCoefficientFamily C y)
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro f
  have hs : ∀ q : Finset A, ∑ a ∈ q, lp.single 2 a (f a) ∈ S.topologicalClosure := by
    intro q
    apply S.topologicalClosure.sum_mem
    intro a _
    apply S.le_topologicalClosure
    exact amplificationCoefficient_continuous_single C y a (f a)
  exact S.isClosed_topologicalClosure.mem_of_tendsto
    (lp.hasSum_single (ENNReal.ofNat_ne_top (n := 2)) f)
    (Filter.Eventually.of_forall hs)

/-- Every amplified coefficient is continuous on each source norm ball. -/
theorem amplificationCoefficient_boundedWOT_continuous (C : ℝ≥0) (y f : ConstantHilbertSum A E) :
    Continuous (fun T : WOTNormBall E C => inner ℂ y (hilbertAmplification T.val.toCLM f)) := by
  have hj : Continuous (fun p : WOTNormBall E C × ConstantHilbertSum A E =>
      amplificationCoefficientFamily C y p.1 p.2) := by
    apply continuous_prod_of_dense_continuous_lipschitzWith' _ (‖y‖₊ * C)
      (amplificationCoefficient_continuous_dense C y)
    · intro T
      apply LipschitzWith.of_dist_le_mul
      intro f g
      rw [dist_eq_norm, dist_eq_norm, ← map_sub]
      change ‖inner ℂ y (hilbertAmplification T.val.toCLM (f - g))‖ ≤ _
      calc
        _ ≤ ‖y‖ * ‖hilbertAmplification T.val.toCLM (f - g)‖ := norm_inner_le_norm _ _
        _ ≤ ‖y‖ * (‖T.val.toCLM‖ * ‖f - g‖) :=
          mul_le_mul_of_nonneg_left (norm_hilbertAmplificationLinear_le T.val.toCLM (f - g)) (norm_nonneg _)
        _ ≤ ‖y‖ * (C * ‖f - g‖) := by
          gcongr
          exact T.property
        _ = _ := by simp only [NNReal.coe_mul, coe_nnnorm]; ring
    · intro f hf
      exact hf
  exact continuous_orbit_of_joint _ hj f

/-- Genuine amplification is WOT continuous on every source operator norm ball. -/
theorem hilbertAmplification_boundedWOT_continuous (C : ℝ≥0) :
    Continuous (fun T : WOTNormBall E C =>
      ContinuousLinearMapWOT.ofCLM (hilbertAmplification (A := A) T.val.toCLM)) := by
  apply ContinuousLinearMapWOT.continuous_iff.mpr
  intro f y
  exact amplificationCoefficient_boundedWOT_continuous C y f

/-- Actual prefix bounded-operator embedding is WOT continuous on each source norm ball. -/
theorem prefixOperatorEmbedding_boundedWOT_continuous {I J : Type*} (C : ℝ≥0) :
    Continuous (fun T : WOTNormBall (WordSpace I) C =>
      ContinuousLinearMapWOT.ofCLM (prefixOperatorEmbedding (J := J) T.val.toCLM)) :=
  (unitaryConjugationWOT_continuous (prefixTailDecomposition (I := I) (J := J)).symm).comp
    (hilbertAmplification_boundedWOT_continuous (A := PrefixTail I J) C)

end FreeProbability.Fock

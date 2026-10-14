import FreeProbability.Analytic.ProjectionProductMoments
import FreeProbability.Analytic.ProjectionTransform

/-! # Actual S-transform germ of a supplied finite free positive family -/

noncomputable section
open scoped BigOperators Topology
namespace FreeProbability
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
namespace StarProbabilitySpace
variable (φ : FreeProbability.StarProbabilitySpace A)

/-- The actual S-transform germ of the identity is the constant one. -/
theorem sTransform_one_eventually :
    φ.sTransform (1 : A) (by simp) =ᶠ[𝓝 0]
      (fun _ => 1) := by
  have hS := φ.sTransform_idempotent_eventually (1 : A) (by simp [IsIdempotentElem])
    (by simp)
  have hc : ContinuousAt (fun w : ℂ => 1 + w) 0 := continuousAt_const.add continuousAt_id
  have hn : ∀ᶠ w : ℂ in 𝓝 0, 1 + w ≠ 0 := hc.eventually_ne (by simp)
  filter_upwards [hS, hn] with w hw hne
  simpa only [φ.toProbabilitySpace.expectation_one, div_self hne] using hw

/-- The S-transform of the actual finite iterated positive product is the
product of all marginal S-transform germs. Original family freeness alone
supplies every prefix-versus-next step. -/
theorem sTransform_iteratedPositiveProduct_eventually (hφ : IsTracial φ.toProbabilitySpace)
    (n : ℕ) {B : Fin n → Subalgebra ℂ A}
    (hf : FreelyIndependent φ.toProbabilitySpace B) (p : Fin n → A)
    (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, 0 ≤ p i)
    (hE : ∀ i, φ.expectation (p i) ≠ 0) :
    φ.sTransform (iteratedPositiveProduct n p)
      (φ.expectation_iteratedPositiveProduct_ne_zero hφ n hf p hpB hp hE) =ᶠ[𝓝 0]
      (fun w => ∏ i, φ.sTransform (p i) (hE i) w) := by
  induction n with
  | zero => simpa [iteratedPositiveProduct] using φ.sTransform_one_eventually
  | succ n ih =>
    have hprefix := φ.expectation_iteratedPositiveProduct_ne_zero hφ n
      (hf.reindex Fin.castSucc (Fin.castSucc_injective n))
      (fun i => p i.castSucc) (fun i => hpB i.castSucc) (fun i => hp i.castSucc)
      (fun i => hE i.castSucc)
    have hstep := φ.sTransform_grouped_positiveMultiplicativeSandwich_eventually hφ hf p hpB
      (fun i => (hp i).isSelfAdjoint) (prefixLastGroup n) Bool.false_ne_true
      (iteratedPositiveProduct n (fun i => p i.castSucc)) (p (Fin.last n))
      (iteratedPositiveProduct_mem_prefixGroup n p hp) (last_mem_prefixGroup n p)
      (iteratedPositiveProduct_nonneg n _ (fun i => hp i.castSucc)) hprefix (hE (Fin.last n))
    have hprev := ih (hf.reindex Fin.castSucc (Fin.castSucc_injective n))
      (fun i => p i.castSucc) (fun i => hpB i.castSucc) (fun i => hp i.castSucc)
      (fun i => hE i.castSucc)
    filter_upwards [hstep, hprev] with w hw hprevw
    change φ.sTransform (positiveMultiplicativeSandwich _ _) _ w = _
    rw [hw, hprevw, Fin.prod_univ_castSucc]
end StarProbabilitySpace
end FreeProbability

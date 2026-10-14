import FreeProbability.Analytic.ProjectionProductS

/-! # Actual rational S germs of supplied finite free projection products -/

noncomputable section
open scoped BigOperators Topology
namespace FreeProbability
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
namespace StarProbabilitySpace
variable (φ : FreeProbability.StarProbabilitySpace A)

/-- Actual free projection products have the rational marginal product germ,
with no assumed product distribution or prefix independence. -/
theorem sTransform_iteratedProjectionProduct_eventually (hφ : IsTracial φ.toProbabilitySpace)
    (n : ℕ) {B : Fin n → Subalgebra ℂ A}
    (hf : FreelyIndependent φ.toProbabilitySpace B) (p : Fin n → A)
    (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, IsStarProjection (p i))
    (hE : ∀ i, φ.expectation (p i) ≠ 0) :
    φ.sTransform (iteratedPositiveProduct n p)
      (φ.expectation_iteratedPositiveProduct_ne_zero hφ n hf p hpB (fun i => (hp i).nonneg) hE)
      =ᶠ[𝓝 0] (fun w => ∏ i, (1 + w) / (φ.expectation (p i) + w)) := by
  have hmain := φ.sTransform_iteratedPositiveProduct_eventually hφ n hf p hpB
    (fun i => (hp i).nonneg) hE
  have hmargin : ∀ᶠ w : ℂ in 𝓝 0,
      ∀ i, φ.sTransform (p i) (hE i) w = (1 + w) / (φ.expectation (p i) + w) :=
    Filter.eventually_all.mpr (fun i =>
      φ.sTransform_idempotent_eventually (p i) (hp i).isIdempotentElem (hE i))
  filter_upwards [hmain, hmargin] with w hw hmw
  rw [hw]
  exact Finset.prod_congr rfl (fun i _ => hmw i)

/-- The actual half-trace projection-product mean is exactly two to the
negative number of factors, including the empty-family normalization. -/
theorem expectation_iteratedHalfProjectionProduct (hφ : IsTracial φ.toProbabilitySpace)
    (n : ℕ) {B : Fin n → Subalgebra ℂ A}
    (hf : FreelyIndependent φ.toProbabilitySpace B) (p : Fin n → A)
    (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, IsStarProjection (p i))
    (hE : ∀ i, φ.expectation (p i) = (1 / 2 : ℂ)) :
    φ.expectation (iteratedPositiveProduct n p) = (1 / 2 : ℂ) ^ n := by
  rw [φ.expectation_iteratedPositiveProduct hφ n hf p hpB (fun i => (hp i).nonneg)]
  simp only [hE, Fin.prod_const]

/-- The genuine S-transform germ of the actual half-trace projection product
is the rational power for every finite number of factors. -/
theorem sTransform_iteratedHalfProjectionProduct_eventually
    (hφ : IsTracial φ.toProbabilitySpace) (n : ℕ) {B : Fin n → Subalgebra ℂ A}
    (hf : FreelyIndependent φ.toProbabilitySpace B) (p : Fin n → A)
    (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, IsStarProjection (p i))
    (hE : ∀ i, φ.expectation (p i) = (1 / 2 : ℂ)) :
    φ.sTransform (iteratedPositiveProduct n p)
      (by rw [φ.expectation_iteratedHalfProjectionProduct hφ n hf p hpB hp hE]; norm_num)
      =ᶠ[𝓝 0] (fun w => ((1 + w) / ((1 / 2 : ℂ) + w)) ^ n) := by
  have h := φ.sTransform_iteratedProjectionProduct_eventually hφ n hf p hpB hp
    (fun i => by rw [hE i]; norm_num)
  simpa only [hE, Fin.prod_const] using h
/-- The selected actual inverse moment germ of the supplied half projections
is the rational germ; this alone makes no claim about its global branch. -/
theorem momentInverse_iteratedHalfProjectionProduct_eventually
    (hφ : IsTracial φ.toProbabilitySpace) (n : ℕ) {B : Fin n → Subalgebra ℂ A}
    (hf : FreelyIndependent φ.toProbabilitySpace B) (p : Fin n → A)
    (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, IsStarProjection (p i))
    (hE : ∀ i, φ.expectation (p i) = (1 / 2 : ℂ)) :
    φ.momentInverse (iteratedPositiveProduct n p)
      (by rw [φ.expectation_iteratedHalfProjectionProduct hφ n hf p hpB hp hE]; norm_num)
      =ᶠ[𝓝 0] (fun w => (w / (1 + w)) * ((1 + w) / ((1 / 2 : ℂ) + w)) ^ n) := by
  let hmean : φ.expectation (iteratedPositiveProduct n p) ≠ 0 := by
    rw [φ.expectation_iteratedHalfProjectionProduct hφ n hf p hpB hp hE]
    norm_num
  have hS := φ.sTransform_iteratedHalfProjectionProduct_eventually hφ n hf p hpB hp hE
  have hc : ContinuousAt (fun w : ℂ => 1 + w) 0 := continuousAt_const.add continuousAt_id
  have hn : ∀ᶠ w : ℂ in 𝓝 0, 1 + w ≠ 0 := hc.eventually_ne (by simp)
  filter_upwards [hS, hn] with w hw hden
  by_cases hz : w = 0
  · simp [hz]
  · have hid : φ.momentInverse (iteratedPositiveProduct n p) hmean w =
        (w / (1 + w)) * φ.sTransform (iteratedPositiveProduct n p) hmean w := by
      rw [φ.sTransform_eq _ hmean w hz]
      field_simp
    rw [hid, hw]
end StarProbabilitySpace
end FreeProbability

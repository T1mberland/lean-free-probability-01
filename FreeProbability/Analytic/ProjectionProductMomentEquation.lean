import FreeProbability.Analytic.ProjectionProductRational

/-! # Genuine local algebraic moment equation for free half projection products -/

noncomputable section
open scoped Topology
namespace FreeProbability
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
namespace StarProbabilitySpace
variable (φ : FreeProbability.StarProbabilitySpace A)

/-- The actual resolvent moment function satisfies the half-projection
polynomial equation near zero, derived from its selected inverse germ. -/
theorem momentGeneratingFunction_iteratedHalfProjectionProduct_equation_eventually
    (hφ : IsTracial φ.toProbabilitySpace) (n : ℕ) {B : Fin (n + 1) → Subalgebra ℂ A}
    (hf : FreelyIndependent φ.toProbabilitySpace B) (p : Fin (n + 1) → A)
    (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, IsStarProjection (p i))
    (hE : ∀ i, φ.expectation (p i) = (1 / 2 : ℂ)) :
    ∀ᶠ z : ℂ in 𝓝 0,
      let w := φ.momentGeneratingFunction (iteratedPositiveProduct (n + 1) p) z
      z * (w + (1 / 2 : ℂ)) ^ (n + 1) = w * (1 + w) ^ n := by
  let a := iteratedPositiveProduct (n + 1) p
  let hmean : φ.expectation a ≠ 0 := by
    rw [φ.expectation_iteratedHalfProjectionProduct hφ (n + 1) hf p hpB hp hE]
    norm_num
  have ht : Filter.Tendsto (φ.momentGeneratingFunction a) (𝓝 0) (𝓝 0) := by
    simpa only [momentGeneratingFunction_zero] using
      (φ.analyticAt_momentGeneratingFunction_zero a).continuousAt.tendsto
  have hχ := ht.eventually (φ.momentInverse_iteratedHalfProjectionProduct_eventually
    hφ (n + 1) hf p hpB hp hE)
  have hone : ∀ᶠ w : ℂ in 𝓝 0, 1 + w ≠ 0 :=
    (continuousAt_const.add continuousAt_id).eventually_ne (by simp)
  have hhalf : ∀ᶠ w : ℂ in 𝓝 0, (1 / 2 : ℂ) + w ≠ 0 :=
    (continuousAt_const.add continuousAt_id).eventually_ne (by norm_num)
  filter_upwards [hχ, φ.momentInverse_eventually_left_inverse a hmean,
    ht.eventually hone, ht.eventually hhalf] with z hχz hinv h1 hh
  change z * (_ + (1 / 2 : ℂ)) ^ (n + 1) = _
  have he : z = (φ.momentGeneratingFunction a z / (1 + φ.momentGeneratingFunction a z)) *
      ((1 + φ.momentGeneratingFunction a z) / ((1 / 2 : ℂ) + φ.momentGeneratingFunction a z)) ^ (n + 1) :=
    hinv.symm.trans hχz
  calc
    z * (φ.momentGeneratingFunction a z + (1 / 2 : ℂ)) ^ (n + 1) =
        ((φ.momentGeneratingFunction a z / (1 + φ.momentGeneratingFunction a z)) *
          ((1 + φ.momentGeneratingFunction a z) /
            ((1 / 2 : ℂ) + φ.momentGeneratingFunction a z)) ^ (n + 1)) *
          (φ.momentGeneratingFunction a z + (1 / 2 : ℂ)) ^ (n + 1) :=
      congrArg (fun u => u * (φ.momentGeneratingFunction a z + (1 / 2 : ℂ)) ^ (n + 1)) he
    _ = φ.momentGeneratingFunction a z * (1 + φ.momentGeneratingFunction a z) ^ n := by
      rw [add_comm (φ.momentGeneratingFunction a z) (1 / 2 : ℂ), div_pow, mul_assoc,
        div_mul_cancel₀ _ (pow_ne_zero (n + 1) hh), pow_succ]
      field_simp [h1]
/-- A genuine change of variable in the actual moment function yields the
positive implicit-series equation used to study the physical branch. -/
theorem normalizedMoment_iteratedHalfProjectionProduct_equation_eventually
    (hφ : IsTracial φ.toProbabilitySpace) (n : ℕ) {B : Fin (n + 1) → Subalgebra ℂ A}
    (hf : FreelyIndependent φ.toProbabilitySpace B) (p : Fin (n + 1) → A)
    (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, IsStarProjection (p i))
    (hE : ∀ i, φ.expectation (p i) = (1 / 2 : ℂ)) :
    ∀ᶠ z : ℂ in 𝓝 0,
      let w := φ.momentGeneratingFunction (iteratedPositiveProduct (n + 1) p) z
      let q := w / (1 + w)
      (2 : ℂ) ^ (n + 1) * q = z * (1 + q) ^ (n + 1) := by
  let a := iteratedPositiveProduct (n + 1) p
  have ht : Filter.Tendsto (φ.momentGeneratingFunction a) (𝓝 0) (𝓝 0) := by
    simpa only [momentGeneratingFunction_zero] using
      (φ.analyticAt_momentGeneratingFunction_zero a).continuousAt.tendsto
  have hn : ∀ᶠ w : ℂ in 𝓝 0, 1 + w ≠ 0 :=
    (continuousAt_const.add continuousAt_id).eventually_ne (by simp)
  filter_upwards [φ.momentGeneratingFunction_iteratedHalfProjectionProduct_equation_eventually
    hφ n hf p hpB hp hE, ht.eventually hn] with z hz hden
  let w := φ.momentGeneratingFunction a z
  change z * (w + (1 / 2 : ℂ)) ^ (n + 1) = w * (1 + w) ^ n at hz
  change 1 + w ≠ 0 at hden
  change (2 : ℂ) ^ (n + 1) * (w / (1 + w)) = z * (1 + w / (1 + w)) ^ (n + 1)
  have hrat : 1 + w / (1 + w) = (2 : ℂ) * (w + (1 / 2 : ℂ)) / (1 + w) := by
    field_simp
    ring
  rw [hrat, div_pow, mul_pow]
  conv_rhs => rw [← mul_div_assoc]
  apply (eq_div_iff (pow_ne_zero (n + 1) hden)).mpr
  calc
    (2 : ℂ) ^ (n + 1) * (w / (1 + w)) * (1 + w) ^ (n + 1) =
        (2 : ℂ) ^ (n + 1) * (w * (1 + w) ^ n) := by
      rw [mul_assoc, pow_succ]
      field_simp [hden]
      rw [pow_succ]
      ring
    _ = (2 : ℂ) ^ (n + 1) * (z * (w + (1 / 2 : ℂ)) ^ (n + 1)) := by rw [hz]
    _ = z * ((2 : ℂ) ^ (n + 1) * (w + (1 / 2 : ℂ)) ^ (n + 1)) := by ring
end StarProbabilitySpace
end FreeProbability

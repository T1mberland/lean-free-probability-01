import FreeProbability.Analytic.ProjectionProductPhysicalPositivity

/-! # The rational curve equation of the actual exterior Cauchy parameter -/

noncomputable section
open scoped Topology NNReal ENNReal
namespace FreeProbability

/-- The intended genuine exterior parameterization curve. -/
def halfProjectionExteriorCurve (L : ℕ) (w : ℝ) : ℝ :=
  (w + (1 / 2 : ℝ)) ^ L / (w * (1 + w) ^ (L - 1))

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
namespace StarProbabilitySpace
variable (φ : FreeProbability.StarProbabilitySpace A)

/-- The ACTUAL law Cauchy parameter satisfies the cleared exterior equation
throughout the full positive exterior, not only near infinity. -/
theorem halfProjectionExteriorW_polynomial_equation
    (hφ : IsTracial φ.toProbabilitySpace) (L : ℕ) (hL : 2 ≤ L)
    {B : Fin L → Subalgebra ℂ A} (hf : FreelyIndependent φ.toProbabilitySpace B)
    (p : Fin L → A) (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, IsStarProjection (p i))
    (hE : ∀ i, φ.expectation (p i) = (1 / 2 : ℂ)) (x : ℝ) (hx : halfProjectionRightEdge L < x) :
    let w := φ.halfProjectionExteriorW L p hp x
    (w + (1 / 2 : ℝ)) ^ L = x * w * (1 + w) ^ (L - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, L = n + 1 := ⟨L - 1, (Nat.sub_add_cancel (by omega)).symm⟩
  let a := iteratedPositiveProduct (n + 1) p
  have ha : 0 ≤ a := iteratedPositiveProduct_nonneg _ p (fun i => (hp i).nonneg)
  have hx0 : 0 < x := (halfProjectionRightEdge_pos _ hL).trans hx
  have hu : 0 < 1 / x := one_div_pos.mpr hx0
  have hut : 1 / x < halfProjectionMomentThreshold (n + 1) := by
    rw [halfProjectionMomentThreshold_eq_reciprocal]
    exact one_div_lt_one_div_of_lt (halfProjectionRightEdge_pos _ hL) hx
  obtain ⟨s, hus, hst⟩ := exists_between hut
  have hs : 0 < s := hu.trans hus
  let sN : ℝ≥0 := ⟨s, hs.le⟩
  have hrad := φ.expectationInverseTaylorSeries_radius_of_spectral_support a ha
    (halfProjectionRightEdge (n + 1)) (halfProjectionRightEdge_pos _ hL).le
    (φ.iteratedHalfProjection_law_support_sharp_upper hφ _ hL hf p hpB hp hE) sN
    ((lt_div_iff₀ (halfProjectionRightEdge_pos _ hL)).mp
      (by change s < 1 / halfProjectionRightEdge (n + 1); simpa only [halfProjectionMomentThreshold_eq_reciprocal] using hst))
  have hpoly := φ.lawMomentSum_iteratedHalfProjection_equation_on_disk hφ n hf p hpB hp hE
    sN (by exact_mod_cast hs) hrad ((1 / x : ℝ) : ℂ)
    (by change ‖((1 / x : ℝ) : ℂ)‖ < s; simpa only [Complex.norm_real, Real.norm_of_nonneg hu.le] using hus)
  rw [φ.lawMomentSum_ofReal a ha.isSelfAdjoint (1 / x)] at hpoly
  let I := φ.lawRealMomentSum a ha.isSelfAdjoint (1 / x)
  change ((1 / x : ℝ) : ℂ) * ((I : ℂ) - (1 / 2 : ℂ)) ^ (n + 1) =
    ((I : ℂ) - 1) * (I : ℂ) ^ n at hpoly
  have he : (1 / x) * (I - (1 / 2 : ℝ)) ^ (n + 1) = (I - 1) * I ^ n := by
    apply Complex.ofReal_injective
    push_cast at hpoly ⊢
    exact hpoly
  have hw : φ.halfProjectionExteriorW (n + 1) p hp x = I - 1 := by
    unfold halfProjectionExteriorW
    rw [φ.iteratedHalfProjection_realCauchyTransform_eq_momentSum hφ _ hL hf p hpB hp hE x hx]
  change (φ.halfProjectionExteriorW (n + 1) p hp x + (1 / 2 : ℝ)) ^ (n + 1) =
    x * φ.halfProjectionExteriorW (n + 1) p hp x * (1 + φ.halfProjectionExteriorW (n + 1) p hp x) ^ n
  rw [hw]
  have hh : I - 1 + (1 / 2 : ℝ) = I - (1 / 2 : ℝ) := by ring
  rw [hh, show 1 + (I - 1) = I by ring]
  have hscaled := congrArg (fun v : ℝ => x * v) he
  simpa only [← mul_assoc, mul_one_div_cancel hx0.ne', one_mul] using hscaled

/-- The literal actual law Cauchy parameter satisfies the desired rational
parameterization on the full right exterior, including length two. -/
theorem halfProjectionExteriorW_curve_equation
    (hφ : IsTracial φ.toProbabilitySpace) (L : ℕ) (hL : 2 ≤ L)
    {B : Fin L → Subalgebra ℂ A} (hf : FreelyIndependent φ.toProbabilitySpace B)
    (p : Fin L → A) (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, IsStarProjection (p i))
    (hE : ∀ i, φ.expectation (p i) = (1 / 2 : ℂ)) (x : ℝ) (hx : halfProjectionRightEdge L < x) :
    halfProjectionExteriorCurve L (φ.halfProjectionExteriorW L p hp x) = x := by
  have hw := φ.halfProjectionExteriorW_pos hφ L hL hf p hpB hp hE x hx
  apply (div_eq_iff (mul_ne_zero hw.ne' (pow_ne_zero (L - 1) (by linarith)))).mpr
  have he := φ.halfProjectionExteriorW_polynomial_equation hφ L hL hf p hpB hp hE x hx
  simpa only [mul_assoc] using he
end StarProbabilitySpace
end FreeProbability

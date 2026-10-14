import FreeProbability.Analytic.TracialDualNormLower
import FreeProbability.Analytic.TracialDualNormSquareRoot

/-! # Tracial Cauchy--Schwarz and the genuine absolute-value dual norm -/

namespace FreeProbability

open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
private theorem expectation_real_smul (φ : StarProbabilitySpace A) (r : ℝ) (a : A) :
    φ.expectation (r • a) = (r : ℂ) * φ.expectation a := by
  rw [← IsScalarTower.algebraMap_smul ℂ r a, map_smul, smul_eq_mul]
  rfl

omit [PartialOrder A] [StarOrderedRing A] in
private theorem expectation_real_algebraMap (φ : StarProbabilitySpace A) (r : ℝ) :
    φ.expectation (algebraMap ℝ A r) = (r : ℂ) := by
  rw [IsScalarTower.algebraMap_eq ℝ ℂ A]
  change φ.expectation (algebraMap ℂ A (r : ℂ)) = (r : ℂ)
  exact φ.toProbabilitySpace.expectation_algebraMap _

theorem tracial_pairing_sq_le_regularized (φ : StarProbabilitySpace A)
    (hφ : IsTracial φ.toProbabilitySpace) (T S : A) (ε : ℝ) (hε : 0 < ε) :
    ‖φ.expectation (S * T)‖ ^ 2 ≤
      ‖S‖ ^ 2 * tracialSize φ T * (tracialSize φ T + ε) := by
  let a := tracialAbsoluteValue T
  let g := tracialRegularizedRootInverse a ε
  let k := tracialRegularizedRoot a ε
  let X := T * g
  let Y := k * S
  have ha : 0 ≤ a := tracialAbsoluteValue_nonneg T
  have hg : star g = g := (IsSelfAdjoint.of_nonneg
    (tracialRegularizedRootInverse_nonneg a ε)).star_eq
  have hk : star k = k := (IsSelfAdjoint.of_nonneg
    (tracialRegularizedRoot_nonneg a ε)).star_eq
  have hgk : g * k = 1 := tracialRegularizedRootInverse_mul_root a ha ε hε
  have hkk : k * k = a + algebraMap ℝ A ε := tracialRegularizedRoot_square a ha ε hε
  have hX : star X * X ≤ a := by
    have he : star X * X = g * (a * a) * g := by
      dsimp [X]
      rw [star_mul, hg, tracialAbsoluteValue_mul_self]
      simp only [mul_assoc]
    rw [he]
    exact tracialRegularizedRootInverse_square_bound a ha ε hε
  have hY : Y * star Y ≤ ‖S‖ ^ 2 • (a + algebraMap ℝ A ε) := by
    have h := star_right_conjugate_le_conjugate
      (CStarAlgebra.mul_star_le_algebraMap_norm_sq S) k
    have he : k * algebraMap ℝ A (‖S‖ ^ 2) * star k =
        ‖S‖ ^ 2 • (a + algebraMap ℝ A ε) := by
      rw [hk, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one,
        smul_mul_assoc, hkk]
    rw [he] at h
    simpa only [Y, star_mul, hk, mul_assoc] using h
  have hpair : φ.expectation (Y * X) = φ.expectation (S * T) := by
    calc
      φ.expectation (Y * X) = φ.expectation ((k * (S * T)) * g) := by
        simp only [Y, X, mul_assoc]
      _ = φ.expectation (g * (k * (S * T))) := hφ _ _
      _ = φ.expectation (S * T) := by rw [← mul_assoc, hgk, one_mul]
  have hx := (φ.toPositiveLinearMap.monotone hX).1
  change (φ.expectation (star X * X)).re ≤ tracialSize φ T at hx
  have hy := (φ.toPositiveLinearMap.monotone hY).1
  change (φ.expectation (Y * star Y)).re ≤
    (φ.expectation (‖S‖ ^ 2 • (a + algebraMap ℝ A ε))).re at hy
  rw [expectation_real_smul, map_add, expectation_real_algebraMap,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.add_re, Complex.ofReal_re] at hy
  have hcs := φ.expectation_star_mul_re_le (star Y) X
  rw [star_star, hpair] at hcs
  have hx0 := φ.expectation_star_mul_self_re_nonneg X
  have hy0 := φ.expectation_star_mul_self_re_nonneg (star Y)
  rw [star_star] at hy0
  have hm := mul_le_mul hy hx hx0 (mul_nonneg (sq_nonneg ‖S‖) (add_nonneg (tracialSize_nonneg φ T) hε.le))
  calc
    ‖φ.expectation (S * T)‖ ^ 2 ≤
        (φ.expectation (Y * star Y)).re * (φ.expectation (star X * X)).re := hcs
    _ ≤ (‖S‖ ^ 2 * (tracialSize φ T + ε)) * tracialSize φ T := hm
    _ = _ := by ring

/-- Tracial Hölder bound for one bounded test operator. -/
theorem tracial_pairing_norm_le (φ : StarProbabilitySpace A)
    (hφ : IsTracial φ.toProbabilitySpace) (T S : A) :
    ‖φ.expectation (S * T)‖ ≤ ‖S‖ * tracialSize φ T := by
  have ha := tracialSize_nonneg φ T
  have hs : 0 ≤ ‖S‖ ^ 2 * tracialSize φ T := mul_nonneg (sq_nonneg _) ha
  have hsq : ‖φ.expectation (S * T)‖ ^ 2 ≤ (‖S‖ * tracialSize φ T) ^ 2 := by
    apply le_of_forall_pos_le_add
    intro δ hδ
    let ε := δ / (‖S‖ ^ 2 * tracialSize φ T + 1)
    have hd : 0 < ‖S‖ ^ 2 * tracialSize φ T + 1 := by linarith
    have hε : 0 < ε := div_pos hδ hd
    have he : ε * (‖S‖ ^ 2 * tracialSize φ T + 1) = δ :=
      div_mul_cancel₀ δ (ne_of_gt hd)
    have h := tracial_pairing_sq_le_regularized φ hφ T S ε hε
    nlinarith
  nlinarith [norm_nonneg (φ.expectation (S * T)), norm_nonneg S,
    mul_nonneg (norm_nonneg S) ha]

/-- The dual norm is exactly the positive trace of the CFC absolute value. -/
theorem tracialDualEmbedding_norm_eq_size (φ : StarProbabilitySpace A)
    (hφ : IsTracial φ.toProbabilitySpace) (T : A) :
    ‖tracialDualEmbedding φ T‖ = tracialSize φ T := by
  apply le_antisymm _ (tracialSize_le_dualNorm φ T)
  apply ContinuousLinearMap.opNorm_le_bound _ (tracialSize_nonneg φ T)
  intro S
  rw [tracialDualEmbedding_apply]
  exact (tracial_pairing_norm_le φ hφ T S).trans_eq (mul_comm _ _)

/-- The absolute-value trace triangle inequality follows from its genuine dual norm. -/
theorem tracialSize_add_le (φ : StarProbabilitySpace A)
    (hφ : IsTracial φ.toProbabilitySpace) (T U : A) :
    tracialSize φ (T + U) ≤ tracialSize φ T + tracialSize φ U := by
  simpa only [tracialDualEmbedding_norm_eq_size φ hφ] using
    tracialDualEmbedding_norm_add_le φ T U

end FreeProbability

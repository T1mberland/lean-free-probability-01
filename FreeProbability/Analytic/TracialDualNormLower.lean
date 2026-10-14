import FreeProbability.Analytic.TracialDualNormRegularization

/-! # Regularized contraction witnesses and the trace-dual lower bound -/

namespace FreeProbability

open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A genuine bounded-algebra contraction approaching the absolute-value pairing. -/
noncomputable def tracialDualWitness (T : A) (ε : ℝ) : A :=
  tracialRegularizedInverse (tracialAbsoluteValue T) ε * star T

theorem tracialDualWitness_mul_star_le (T : A) (ε : ℝ) (hε : 0 < ε) :
    tracialDualWitness T ε * star (tracialDualWitness T ε) ≤ 1 := by
  have hq := (IsSelfAdjoint.of_nonneg (tracialRegularizedInverse_nonneg
    (tracialAbsoluteValue T) (tracialAbsoluteValue_nonneg T) ε hε)).star_eq
  have he : tracialDualWitness T ε * star (tracialDualWitness T ε) =
      tracialRegularizedInverse (tracialAbsoluteValue T) ε *
        (tracialAbsoluteValue T * tracialAbsoluteValue T) *
        tracialRegularizedInverse (tracialAbsoluteValue T) ε := by
    rw [tracialDualWitness, star_mul, star_star, hq,
      tracialAbsoluteValue_mul_self]
    simp only [mul_assoc]
  rw [he]
  exact tracialRegularizedInverse_square_bound _ (tracialAbsoluteValue_nonneg T) ε hε

theorem tracialDualWitness_norm_le (φ : StarProbabilitySpace A) (T : A)
    (ε : ℝ) (hε : 0 < ε) : ‖tracialDualWitness T ε‖ ≤ 1 := by
  let _ : Nontrivial A := φ.toProbabilitySpace.nontrivial
  have h := CStarAlgebra.norm_le_norm_of_le_of_nonneg
    (tracialDualWitness_mul_star_le T ε hε) (mul_star_self_nonneg (tracialDualWitness T ε))
  rw [CStarRing.norm_self_mul_star, norm_one] at h
  nlinarith [norm_nonneg (tracialDualWitness T ε)]

theorem tracialDualWitness_pairing_lower (φ : StarProbabilitySpace A) (T : A)
    (ε : ℝ) (hε : 0 < ε) :
    tracialSize φ T - ε ≤ (φ.expectation (tracialDualWitness T ε * T)).re := by
  have h := φ.toPositiveLinearMap.monotone
    (tracialRegularizedInverse_lower_bound _ (tracialAbsoluteValue_nonneg T) ε hε)
  have he : tracialDualWitness T ε * T =
      tracialRegularizedInverse (tracialAbsoluteValue T) ε *
        (tracialAbsoluteValue T * tracialAbsoluteValue T) := by
    rw [tracialDualWitness, tracialAbsoluteValue_mul_self, mul_assoc]
  have hm : φ.expectation (algebraMap ℝ A ε) = (ε : ℂ) := by
    rw [IsScalarTower.algebraMap_eq ℝ ℂ A]
    change φ.expectation (algebraMap ℂ A (ε : ℂ)) = (ε : ℂ)
    exact φ.toProbabilitySpace.expectation_algebraMap _
  rw [← he] at h
  have hr := h.1
  change (φ.expectation (tracialAbsoluteValue T - algebraMap ℝ A ε)).re ≤ _ at hr
  rw [map_sub, hm, Complex.sub_re, Complex.ofReal_re] at hr
  exact hr

theorem tracialSize_le_dualNorm (φ : StarProbabilitySpace A) (T : A) :
    tracialSize φ T ≤ ‖tracialDualEmbedding φ T‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hl := tracialDualWitness_pairing_lower φ T ε hε
  have hu := (tracialDualEmbedding φ T).le_opNorm (tracialDualWitness T ε)
  rw [tracialDualEmbedding_apply] at hu
  have hw := tracialDualWitness_norm_le φ T ε hε
  have hn := norm_nonneg (tracialDualEmbedding φ T)
  have hb := Complex.re_le_norm (φ.expectation (tracialDualWitness T ε * T))
  nlinarith

end FreeProbability

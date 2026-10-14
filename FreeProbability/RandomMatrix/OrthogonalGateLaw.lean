import FreeProbability.RandomMatrix.GaussianSigns

/-! # Exact one-step ReLU gate law for a nonzero Haar input -/

namespace FreeProbability.Orthogonal

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
theorem positiveSet_smul (a : ℝ) (ha : 0 < a) (x : n → ℝ) : positiveSet (a • x) = positiveSet x := by
  ext i
  change (0 < a * x i) ↔ 0 < x i
  exact mul_pos_iff_of_pos_left ha

omit [DecidableEq n] in
theorem positiveSet_direction (x : n → ℝ) : positiveSet (direction x) = positiveSet x := by
  by_cases hx : x = 0
  · subst x
    rw [direction_zero]
  · exact positiveSet_smul _ (inv_pos.mpr (norm_pos_iff.mpr (by simpa using hx))) x

/-- The complete gate mask of a Haar image of any nonzero input consists of
independent half-Bernoulli coordinates. Zero input is explicitly excluded. -/
theorem vectorLaw_map_positiveSet (x : n → ℝ) (hx : x ≠ 0) :
    (vectorLaw x).map positiveSet = setBernoulli Set.univ halfProbability := by
  classical
  obtain ⟨r, _⟩ := Function.ne_iff.mp hx
  let _ : Nonempty n := ⟨r⟩
  have hn : 0 < ‖WithLp.toLp 2 x‖ := norm_pos_iff.mpr (by simpa using hx)
  have hm : Measurable (fun g : n → ℝ => ‖WithLp.toLp 2 x‖ • direction g) :=
    (measurable_const_smul _).comp measurable_direction
  rw [vectorLaw_eq_normalized_gaussian, Measure.map_map measurable_positiveSet hm]
  have he : (positiveSet ∘ (fun g : n → ℝ => ‖WithLp.toLp 2 x‖ • direction g)) = positiveSet := by
    funext g
    rw [Function.comp_apply, positiveSet_smul _ hn, positiveSet_direction]
  rw [he, gaussianVector_map_positiveSet]

theorem vectorLaw_positiveSet_singleton (x : n → ℝ) (hx : x ≠ 0) (S : Set n) :
    (vectorLaw x).map positiveSet {S} = (1 / 2 : ℝ≥0∞) ^ Fintype.card n := by
  rw [vectorLaw_map_positiveSet x hx, setBernoulli_univ_half_singleton]

/-- The gate count has the actual binomial probability measure in every dimension. -/
theorem vectorLaw_map_gateRank (x : n → ℝ) (hx : x ≠ 0) :
    (vectorLaw x).map gateRank = binomial (Fintype.card n) halfProbability := by
  have hm : Measurable (Set.ncard : Set n → ℕ) := by fun_prop
  have he : gateRank (n := n) = Set.ncard ∘ positiveSet := rfl
  rw [he, ← Measure.map_map hm measurable_positiveSet, vectorLaw_map_positiveSet x hx]
  apply Measure.ext_of_measureReal_singleton
  intro k
  rw [map_ncard_setBernoulli_real_singleton (Set.toFinite Set.univ), binomial_real_singleton]
  simp only [Set.ncard_univ, Nat.card_eq_fintype_card]

theorem gateRank_haar_hasLaw (x : n → ℝ) (hx : x ≠ 0) :
    HasLaw (fun U : Group n => gateRank ((U : Matrix n n ℝ) *ᵥ x))
      (binomial (Fintype.card n) halfProbability) (haar n) := by
  refine ⟨(measurable_gateRank.comp (continuous_mulVec x).measurable).aemeasurable, ?_⟩
  have hm := Measure.map_map measurable_gateRank (continuous_mulVec x).measurable (μ := haar n)
  simp only [Function.comp_def] at hm
  rw [← hm]
  exact vectorLaw_map_gateRank x hx

theorem positiveSet_haar_hasLaw (x : n → ℝ) (hx : x ≠ 0) :
    HasLaw (fun U : Group n => positiveSet ((U : Matrix n n ℝ) *ᵥ x))
      (setBernoulli Set.univ halfProbability) (haar n) := by
  refine ⟨(measurable_positiveSet.comp (continuous_mulVec x).measurable).aemeasurable, ?_⟩
  have hm := Measure.map_map measurable_positiveSet (continuous_mulVec x).measurable (μ := haar n)
  simp only [Function.comp_def] at hm
  rw [← hm]
  exact vectorLaw_map_positiveSet x hx

theorem haar_gateRank_real_probability (x : n → ℝ) (hx : x ≠ 0) (k : ℕ) :
    (haar n).real {U | gateRank ((U : Matrix n n ℝ) *ᵥ x) = k} =
      (Fintype.card n).choose k * (1 / 2 : ℝ) ^ k * (1 / 2 : ℝ) ^ (Fintype.card n - k) := by
  have h := (gateRank_haar_hasLaw x hx).measureReal_eq
    (p := fun j => j = k) (measurableSet_singleton _)
  change _ = (binomial (Fintype.card n) halfProbability).real {k} at h
  rw [binomial_real_singleton] at h
  have hh : (1 : ℝ) - halfProbability = 1 / 2 := by norm_num [halfProbability]
  rw [hh] at h
  simpa [halfProbability] using h

theorem haar_gateRank_extreme_probability (x : n → ℝ) (hx : x ≠ 0) :
    (haar n).real {U | gateRank ((U : Matrix n n ℝ) *ᵥ x) = 0 ∨
      gateRank ((U : Matrix n n ℝ) *ᵥ x) = Fintype.card n} =
        2 * (1 / 2 : ℝ) ^ Fintype.card n := by
  obtain ⟨r, _⟩ := Function.ne_iff.mp hx
  let _ : Nonempty n := ⟨r⟩
  have hn : Fintype.card n ≠ 0 := Fintype.card_ne_zero
  have hd : Disjoint ({0} : Set ℕ) {Fintype.card n} := by
    apply Set.disjoint_left.mpr
    intro k hk0 hkN
    simp only [Set.mem_singleton_iff] at hk0 hkN
    exact hn (hkN.symm.trans hk0)
  have he : {k : ℕ | k = 0 ∨ k = Fintype.card n} = ({0} : Set ℕ) ∪ {Fintype.card n} := by
    ext k
    simp [or_comm]
  have hm : MeasurableSet {k : ℕ | k = 0 ∨ k = Fintype.card n} := by
    rw [he]
    exact (measurableSet_singleton _).union (measurableSet_singleton _)
  have h := (gateRank_haar_hasLaw x hx).measureReal_eq hm
  rw [he, measureReal_union hd (measurableSet_singleton _), binomial_real_zero,
    binomial_real_self] at h
  have hh : (1 : ℝ) - halfProbability = 1 / 2 := by norm_num [halfProbability]
  rw [hh] at h
  calc
    _ = (1 / 2 : ℝ) ^ Fintype.card n + (1 / 2 : ℝ) ^ Fintype.card n := by
      simpa [halfProbability] using h
    _ = _ := by ring

end FreeProbability.Orthogonal

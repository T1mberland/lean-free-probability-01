import FreeProbability.RandomMatrix.FreshHaarInput
import FreeProbability.Applications.ReLU.ForwardEnergy

/-! # Extinction probabilities for fresh Haar ReLU layers -/

namespace FreeProbability.ReLU

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem gateProjection_mulVec_eq_zero_iff (v : n → ℝ) :
    gateProjection v *ᵥ v = 0 ↔ Orthogonal.gateRank v = 0 := by
  rw [gateProjection_mulVec]
  constructor
  · intro h
    apply (Set.ncard_eq_zero (Set.toFinite _)).mpr
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have he := congrFun h i
    change max 0 (v i) = 0 at he
    change 0 < v i at hi
    rw [max_eq_right hi.le] at he
    exact hi.ne' he
  · intro h
    have he : Orthogonal.positiveSet v = ∅ := (Set.ncard_eq_zero (Set.toFinite _)).mp h
    funext i
    have hi : v i ≤ 0 := by
      by_contra hn
      have hm : i ∈ Orthogonal.positiveSet v := lt_of_not_ge hn
      rw [he] at hm
      exact Set.notMem_empty i hm
    exact max_eq_left hi

theorem haar_gateProjection_mulVec_zero_probability (x : n → ℝ) (hx : x ≠ 0) :
    (Orthogonal.haar n) {U | gateProjection ((U : Matrix n n ℝ) *ᵥ x) *ᵥ
      ((U : Matrix n n ℝ) *ᵥ x) = 0} = ENNReal.ofReal ((1 / 2 : ℝ) ^ Fintype.card n) := by
  have h := Orthogonal.haar_gateRank_real_probability x hx 0
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul, Nat.sub_zero] at h
  have he : {U : Orthogonal.Group n | gateProjection ((U : Matrix n n ℝ) *ᵥ x) *ᵥ
      ((U : Matrix n n ℝ) *ᵥ x) = 0} =
        {U : Orthogonal.Group n | Orthogonal.gateRank ((U : Matrix n n ℝ) *ᵥ x) = 0} := by
    ext U
    exact gateProjection_mulVec_eq_zero_iff _
  rw [he, ← ofReal_measureReal (μ := Orthogonal.haar n), h]

theorem fresh_haar_gateProjection_mulVec_zero_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → (n → ℝ)) (hX : Measurable X) :
    μ.prod (Orthogonal.haar n) {p | gateProjection (Orthogonal.freshHaarImage X p) *ᵥ
      Orthogonal.freshHaarImage X p = 0} ≤
        μ {ω | X ω = 0} + ENNReal.ofReal ((1 / 2 : ℝ) ^ Fintype.card n) := by
  have hrelu : Measurable (fun v : n → ℝ => gateProjection v *ᵥ v) := by
    simp only [gateProjection_mulVec]
    fun_prop
  have hm := (hrelu.comp (Orthogonal.measurable_freshHaarImage X hX)) (measurableSet_singleton 0)
  apply measure_prod_event_le_of_fiber_bound μ (Orthogonal.haar n) _ hm _
    (hX (measurableSet_singleton 0)) _
  intro ω hω
  exact (haar_gateProjection_mulVec_zero_probability (X ω) hω).le

end FreeProbability.ReLU

import FreeProbability.RandomMatrix.OrthogonalGateLaw
import FreeProbability.RandomMatrix.AlmostSureFromTails
import Mathlib.Probability.Moments.SubGaussian

/-! # Exponential concentration of the actual Haar gate count -/

namespace FreeProbability.Orthogonal

open Matrix MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal

noncomputable def positiveIndicator : ℝ → ℝ := (Ioi 0).indicator (fun _ => 1)

theorem measurable_positiveIndicator : Measurable positiveIndicator :=
  measurable_const.indicator measurableSet_Ioi

theorem positiveIndicator_mem_Icc (x : ℝ) : positiveIndicator x ∈ Icc (0 : ℝ) 1 := by
  by_cases hx : 0 < x <;> simp [positiveIndicator, hx]

theorem integral_positiveIndicator : (∫ x, positiveIndicator x ∂gaussianReal 0 1) = (1 / 2 : ℝ) := by
  rw [positiveIndicator, integral_indicator_const (1 : ℝ) measurableSet_Ioi]
  simp only [smul_eq_mul, mul_one, gaussianReal_positive_half]

theorem positiveIndicator_subgaussian :
    HasSubgaussianMGF (fun x => positiveIndicator x - 1 / 2) (1 / 4 : ℝ≥0) (gaussianReal 0 1) := by
  have h := hasSubgaussianMGF_of_mem_Icc (μ := gaussianReal 0 1) measurable_positiveIndicator.aemeasurable
    (Filter.Eventually.of_forall positiveIndicator_mem_Icc)
  rw [integral_positiveIndicator] at h
  norm_num at h
  exact h

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem gaussianVector_map_eval (i : n) :
    (gaussianVector n).map (Function.eval i) = gaussianReal 0 1 := by
  simp [gaussianVector, Measure.pi_map_eval]

omit [DecidableEq n] in
theorem gateRank_eq_sum_positiveIndicator (g : n → ℝ) :
    (gateRank g : ℝ) = ∑ i, positiveIndicator (g i) := by
  classical
  have hc : gateRank g = Fintype.card {i : n // 0 < g i} :=
    (Set.fintypeCard_eq_ncard (positiveSet g)).symm
  rw [hc]
  simp [positiveIndicator, Set.indicator, Fintype.card_subtype]

theorem centered_gateRank_subgaussian :
    HasSubgaussianMGF (fun g : n → ℝ => (gateRank g : ℝ) - (Fintype.card n : ℝ) / 2)
      (∑ _i : n, (1 / 4 : ℝ≥0)) (gaussianVector n) := by
  let X := fun i : n => fun g : n → ℝ => positiveIndicator (g i) - 1 / 2
  have hm : AEMeasurable (fun x : ℝ => positiveIndicator x - 1 / 2) (gaussianReal 0 1) :=
    measurable_positiveIndicator.sub measurable_const |>.aemeasurable
  have hind : iIndepFun X (gaussianVector n) := by
    simpa [X, gaussianVector] using iIndepFun_pi (fun _i : n => hm)
  have hs (i : n) : HasSubgaussianMGF (X i) (1 / 4 : ℝ≥0) (gaussianVector n) := by
    have h : HasSubgaussianMGF (fun x => positiveIndicator x - 1 / 2) (1 / 4 : ℝ≥0)
        ((gaussianVector n).map (Function.eval i)) := by
      rw [gaussianVector_map_eval]
      exact positiveIndicator_subgaussian
    have he : AEMeasurable (Function.eval i) (gaussianVector n) :=
      (measurable_pi_apply i).aemeasurable
    exact HasSubgaussianMGF.of_map he h
  have h := HasSubgaussianMGF.sum_of_iIndepFun hind (s := Finset.univ) (fun i _ => hs i)
  apply h.congr
  apply Filter.Eventually.of_forall
  intro g
  simp only [X, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← gateRank_eq_sum_positiveIndicator]
  ring

theorem subgaussian_measure_abs_ge_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0} (hX : HasSubgaussianMGF X c μ)
    (ε : ℝ) (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |X ω|} ≤ 2 * exp (-ε ^ 2 / (2 * c)) := by
  have he : {ω | ε ≤ |X ω|} = {ω | ε ≤ X ω} ∪ {ω | ε ≤ -X ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, le_abs]
  rw [he]
  have hn : μ.real {ω | ε ≤ -X ω} ≤ exp (-ε ^ 2 / (2 * c)) := by
    simpa only [Pi.neg_apply] using hX.neg.measure_ge_le hε
  calc
    _ ≤ μ.real {ω | ε ≤ X ω} + μ.real {ω | ε ≤ -X ω} := measureReal_union_le _ _
    _ ≤ exp (-ε ^ 2 / (2 * c)) + exp (-ε ^ 2 / (2 * c)) := add_le_add (hX.measure_ge_le hε) hn
    _ = _ := by ring

/-- Hoeffding's exact exponential rate for the normalized Gaussian gate count. -/
theorem gaussianVector_gateRank_deviation_le [Nonempty n] (ε : ℝ) (hε : 0 ≤ ε) :
    (gaussianVector n).real {g | ε ≤ |(gateRank g : ℝ) / (Fintype.card n : ℝ) - 1 / 2|} ≤
      2 * exp (-2 * (Fintype.card n : ℝ) * ε ^ 2) := by
  have hN : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hc : ((∑ _i : n, (1 / 4 : ℝ≥0)) : ℝ) = (Fintype.card n : ℝ) / 4 := by
    simp [nsmul_eq_mul, div_eq_mul_inv]
  have h := subgaussian_measure_abs_ge_le (centered_gateRank_subgaussian (n := n))
    ((Fintype.card n : ℝ) * ε) (mul_nonneg hN.le hε)
  simp only [NNReal.coe_sum] at h
  rw [hc] at h
  have hrel (g : n → ℝ) : (gateRank g : ℝ) - (Fintype.card n : ℝ) / 2 =
      (Fintype.card n : ℝ) * ((gateRank g : ℝ) / (Fintype.card n : ℝ) - 1 / 2) := by
    field_simp [hN.ne']
  have he : {g : n → ℝ | (Fintype.card n : ℝ) * ε ≤
      |(gateRank g : ℝ) - (Fintype.card n : ℝ) / 2|} =
        {g | ε ≤ |(gateRank g : ℝ) / (Fintype.card n : ℝ) - 1 / 2|} := by
    ext g
    simp only [Set.mem_ofPred_eq]
    rw [hrel, abs_mul, abs_of_pos hN]
    exact mul_le_mul_iff_of_pos_left hN
  have hexp : -((Fintype.card n : ℝ) * ε) ^ 2 / (2 * ((Fintype.card n : ℝ) / 4)) =
      -2 * (Fintype.card n : ℝ) * ε ^ 2 := by
    field_simp [hN.ne']
    ring
  rw [he, hexp] at h
  exact h

theorem haar_gateRank_deviation_le (x : n → ℝ) (hx : x ≠ 0) (ε : ℝ) (hε : 0 ≤ ε) :
    (haar n).real {U | ε ≤ |(gateRank ((U : Matrix n n ℝ) *ᵥ x) : ℝ) /
      (Fintype.card n : ℝ) - 1 / 2|} ≤ 2 * exp (-2 * (Fintype.card n : ℝ) * ε ^ 2) := by
  obtain ⟨r, _⟩ := Function.ne_iff.mp hx
  let _ : Nonempty n := ⟨r⟩
  have hg : HasLaw (gateRank (n := n)) (binomial (Fintype.card n) halfProbability) (gaussianVector n) :=
    ⟨measurable_gateRank.aemeasurable, gaussianVector_map_gateRank⟩
  have hm : MeasurableSet {k : ℕ | ε ≤ |(k : ℝ) / (Fintype.card n : ℝ) - 1 / 2|} := .of_discrete
  rw [(gateRank_haar_hasLaw x hx).measureReal_eq hm, ← hg.measureReal_eq hm]
  exact gaussianVector_gateRank_deviation_le ε hε

theorem binomial_half_deviation_le (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 ≤ ε) :
    (binomial N halfProbability).real {k : ℕ | ε ≤ |(k : ℝ) / (N : ℝ) - 1 / 2|} ≤
      2 * exp (-2 * (N : ℝ) * ε ^ 2) := by
  let _ : NeZero N := ⟨hN.ne'⟩
  have hg : HasLaw (gateRank (n := Fin N)) (binomial N halfProbability) (gaussianVector (Fin N)) :=
    ⟨measurable_gateRank.aemeasurable, by simpa using gaussianVector_map_gateRank (n := Fin N)⟩
  have hm : MeasurableSet {k : ℕ | ε ≤ |(k : ℝ) / (N : ℝ) - 1 / 2|} := .of_discrete
  rw [← hg.measureReal_eq hm]
  simpa using gaussianVector_gateRank_deviation_le (n := Fin N) ε hε

end FreeProbability.Orthogonal

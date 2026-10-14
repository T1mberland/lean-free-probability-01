import FreeProbability.RandomMatrix.OrthogonalGaussianDirection
import Mathlib.Probability.Distributions.SetBernoulli
import Mathlib.Probability.Distributions.Binomial

/-! # Independent standard Gaussian signs and gate masks -/

namespace FreeProbability.Orthogonal

open Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

theorem gaussianReal_positive_half : (gaussianReal 0 1).real (Ioi 0) = (1 / 2 : ℝ) := by
  let _ : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  have hneg : (gaussianReal 0 1).map (fun x : ℝ => -x) = gaussianReal 0 1 := by
    simpa using (gaussianReal_map_neg (μ := 0) (v := 1))
  have hsym := congrArg (fun μ : Measure ℝ => μ.real (Ioi 0)) hneg
  rw [map_measureReal_apply (measurable_neg) measurableSet_Ioi] at hsym
  have he : (fun x : ℝ => -x) ⁻¹' Ioi 0 = Iio 0 := by ext x; simp
  rw [he] at hsym
  have hd : Disjoint (Iio (0 : ℝ)) (Ioi 0) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    change x < 0 at hx
    change 0 < x at hy
    linarith
  have hsum := measureReal_union (μ := gaussianReal 0 1) hd measurableSet_Ioi
  rw [Iio_union_Ioi, probReal_compl_eq_one_sub (measurableSet_singleton _)] at hsum
  have h0 : (gaussianReal 0 1).real {(0 : ℝ)} = 0 := by simp [measureReal_def]
  rw [h0, sub_zero] at hsum
  linarith

theorem gaussianReal_nonpositive_half : (gaussianReal 0 1).real (Iic 0) = (1 / 2 : ℝ) := by
  have h := probReal_add_probReal_compl (μ := gaussianReal 0 1) (s := Ioi 0) measurableSet_Ioi
  rw [compl_Ioi, gaussianReal_positive_half] at h
  linarith

theorem gaussianReal_positive_half_measure : gaussianReal 0 1 (Ioi 0) = (1 / 2 : ℝ≥0∞) := by
  have h := congrArg ENNReal.ofReal gaussianReal_positive_half
  rw [ofReal_measureReal (μ := gaussianReal 0 1) (s := Ioi 0)] at h
  simpa using h

theorem gaussianReal_nonpositive_half_measure : gaussianReal 0 1 (Iic 0) = (1 / 2 : ℝ≥0∞) := by
  have h := congrArg ENNReal.ofReal gaussianReal_nonpositive_half
  rw [ofReal_measureReal (μ := gaussianReal 0 1) (s := Iic 0)] at h
  simpa using h

variable {n : Type*} [Fintype n] [DecidableEq n]

def positiveSet (x : n → ℝ) : Set n := {i | 0 < x i}

omit [Fintype n] [DecidableEq n] in
theorem measurable_positiveSet : Measurable (positiveSet (n := n)) := by
  change Measurable (fun x : n → ℝ => fun i : n => 0 < x i)
  apply measurable_pi_iff.mpr
  intro i
  exact measurableSet_setOfPred.mp (measurableSet_lt measurable_const (measurable_pi_apply i))

omit [Fintype n] [DecidableEq n] in
theorem positiveSet_preimage_singleton (S : Set n) [DecidablePred (fun i => i ∈ S)] :
    positiveSet ⁻¹' {S} = Set.univ.pi (fun i => if i ∈ S then Ioi (0 : ℝ) else Iic 0) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ_pi]
  constructor
  · intro h i
    have hi := Set.ext_iff.mp h i
    change (0 < x i) ↔ i ∈ S at hi
    by_cases hS : i ∈ S
    · simpa [hS] using hi.mpr hS
    · have hn : ¬0 < x i := fun hx => hS (hi.mp hx)
      simpa [hS] using le_of_not_gt hn
  · intro h
    ext i
    have hi := h i
    by_cases hS : i ∈ S <;> simp [positiveSet, hS] at hi ⊢ <;> exact hi

omit [DecidableEq n] in
/-- Every Gaussian coordinate sign pattern has the same exact probability. -/
theorem gaussianVector_positiveSet_singleton (S : Set n) :
    (gaussianVector n).map positiveSet {S} = (1 / 2 : ℝ≥0∞) ^ Fintype.card n := by
  classical
  rw [Measure.map_apply measurable_positiveSet (measurableSet_singleton _),
    positiveSet_preimage_singleton, gaussianVector, Measure.pi_pi]
  have he (i : n) : gaussianReal 0 1 (if i ∈ S then Ioi (0 : ℝ) else Iic 0) = (1 / 2 : ℝ≥0∞) := by
    by_cases hi : i ∈ S
    · simpa only [ite_eq_left hi] using gaussianReal_positive_half_measure
    · simpa only [ite_eq_right hi] using gaussianReal_nonpositive_half_measure
  simp_rw [he]
  simp

noncomputable def halfProbability : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩

omit [DecidableEq n] in
theorem setBernoulli_univ_half_singleton (S : Set n) :
    setBernoulli Set.univ halfProbability {S} = (1 / 2 : ℝ≥0∞) ^ Fintype.card n := by
  classical
  rw [setBernoulli_singleton halfProbability (Set.subset_univ _) (Set.toFinite _)]
  have hh : (unitInterval.toNNReal halfProbability : ℝ≥0∞) = (1 / 2 : ℝ≥0∞) := by
    have hn : unitInterval.toNNReal halfProbability = (1 / 2 : ℝ≥0) := by
      apply Subtype.ext
      norm_num [halfProbability, unitInterval.toNNReal]
    rw [hn, ENNReal.coe_div] <;> norm_num
  have hh' : (unitInterval.toNNReal (unitInterval.symm halfProbability) : ℝ≥0∞) =
      (1 / 2 : ℝ≥0∞) := by
    have hs : unitInterval.symm halfProbability = halfProbability := by
      apply Subtype.ext
      norm_num [halfProbability, unitInterval.symm]
    rw [hs]
    exact hh
  rw [hh, hh', ← pow_add]
  congr 1
  have he : (Set.univ : Set n) \ S = Sᶜ := by ext i; simp
  rw [he]
  simpa only [Nat.card_eq_fintype_card] using Set.ncard_add_ncard_compl S

omit [DecidableEq n] in
/-- The whole Gaussian sign mask has the independent half-Bernoulli set law. -/
theorem gaussianVector_map_positiveSet :
    (gaussianVector n).map positiveSet = setBernoulli Set.univ halfProbability := by
  apply Measure.ext_of_singleton
  intro S
  rw [gaussianVector_positiveSet_singleton, setBernoulli_univ_half_singleton]

noncomputable def gateRank (x : n → ℝ) : ℕ := (positiveSet x).ncard

omit [DecidableEq n] in
theorem measurable_gateRank : Measurable (gateRank (n := n)) := by
  exact (by fun_prop : Measurable (Set.ncard : Set n → ℕ)).comp measurable_positiveSet

omit [DecidableEq n] in
theorem gaussianVector_map_gateRank :
    (gaussianVector n).map gateRank = binomial (Fintype.card n) halfProbability := by
  have hm : Measurable (Set.ncard : Set n → ℕ) := by fun_prop
  have he : gateRank (n := n) = Set.ncard ∘ positiveSet := rfl
  rw [he, ← Measure.map_map hm measurable_positiveSet, gaussianVector_map_positiveSet]
  apply Measure.ext_of_measureReal_singleton
  intro k
  rw [map_ncard_setBernoulli_real_singleton (Set.toFinite Set.univ), binomial_real_singleton]
  simp only [Set.ncard_univ, Nat.card_eq_fintype_card]

end FreeProbability.Orthogonal

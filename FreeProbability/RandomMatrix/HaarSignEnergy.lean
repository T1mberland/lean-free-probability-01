import FreeProbability.RandomMatrix.GaussianSignEnergy

/-! # Summable Haar positive-sign energy deviations -/

namespace FreeProbability.Orthogonal

open Matrix MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

theorem ratio_half_deviation_implies (A B ε t : ℝ) (ht : 0 < t)
    (hhalf : t ≤ 1 / 2) (heps : 4 * t ≤ ε) (hbad : ε ≤ |A / B - 1 / 2|) :
    t ≤ |A - 1 / 2| ∨ t ≤ |B - 1| := by
  by_contra h
  rcases not_or.mp h with ⟨hA, hB⟩
  rcases abs_lt.mp (lt_of_not_ge hA) with ⟨hAl, hAu⟩
  rcases abs_lt.mp (lt_of_not_ge hB) with ⟨hBl, hBu⟩
  have hBhalf : 1 / 2 ≤ B := by linarith
  have hBpos : 0 < B := by linarith
  have hε : 0 ≤ ε := by linarith
  have hεB : 2 * t ≤ ε * B := by
    have hmul := mul_le_mul_of_nonneg_left hBhalf hε
    nlinarith
  have hsmall : |A / B - 1 / 2| < ε := by
    apply abs_lt.mpr
    constructor
    · rw [lt_sub_iff_add_lt, lt_div_iff₀ hBpos]
      nlinarith
    · rw [sub_lt_iff_lt_add, div_lt_iff₀ hBpos]
      nlinarith
  exact (not_lt_of_ge hbad) hsmall

noncomputable def energyFourthMomentBound : ℝ :=
  averageFourthMomentBound (gaussianReal 0 1) positiveSquared +
    averageFourthMomentBound (gaussianReal 0 1) (fun x : ℝ => x ^ 2)

theorem energyFourthMomentBound_nonneg : 0 ≤ energyFourthMomentBound :=
  add_nonneg (averageFourthMomentBound_nonneg _ _) (averageFourthMomentBound_nonneg _ _)

noncomputable def energyDeviationThreshold (ε : ℝ) : ℝ := min (1 / 2) (ε / 4)

theorem energyDeviationThreshold_pos {ε : ℝ} (hε : 0 < ε) : 0 < energyDeviationThreshold ε :=
  lt_min (by norm_num) (by positivity)

theorem gaussian_positiveEnergyFraction_deviation_le {n : Type*} [Fintype n]
    (hN : (0 : ℝ) < Fintype.card n) (ε : ℝ) (hε : 0 < ε) :
    (gaussianVector n) {g | ε ≤ |positiveEnergyFraction g - 1 / 2|} ≤
      ENNReal.ofReal (energyFourthMomentBound /
        ((Fintype.card n : ℝ) ^ 2 * energyDeviationThreshold ε ^ 4)) := by
  classical
  let t := energyDeviationThreshold ε
  have ht : 0 < t := energyDeviationThreshold_pos hε
  have hp := measure_product_average_deviation_le (gaussianReal 0 1) positiveSquared
    continuous_positiveSquared.measurable gaussian_positiveSquared_memLp_four hN t ht
  have hs := measure_product_average_deviation_le (gaussianReal 0 1) (fun x : ℝ => x ^ 2)
    (measurable_id.pow_const 2) gaussian_sq_memLp_four hN t ht
  simp only [integral_gaussian_positiveSquared] at hp
  simp only [integral_gaussian_sq] at hs
  let Sp := {g : n → ℝ | t ≤ |(∑ i, positiveSquared (g i)) / (Fintype.card n : ℝ) - 1 / 2|}
  let Ss := {g : n → ℝ | t ≤ |(∑ i, g i ^ 2) / (Fintype.card n : ℝ) - 1|}
  have hsub : {g : n → ℝ | ε ≤ |positiveEnergyFraction g - 1 / 2|} ⊆ Sp ∪ Ss := by
    intro g hg
    have he : ((∑ i, positiveSquared (g i)) / (Fintype.card n : ℝ)) /
        ((∑ i, g i ^ 2) / (Fintype.card n : ℝ)) = positiveEnergyFraction g :=
      div_div_div_cancel_right₀ hN.ne' _ _
    change ε ≤ |positiveEnergyFraction g - 1 / 2| at hg
    rw [← he] at hg
    exact ratio_half_deviation_implies _ _ ε t ht (min_le_left _ _)
      (by have h := min_le_right (1 / 2 : ℝ) (ε / 4); dsimp [t, energyDeviationThreshold]; linarith) hg
  calc
    _ ≤ (gaussianVector n) (Sp ∪ Ss) := measure_mono hsub
    _ ≤ (gaussianVector n) Sp + (gaussianVector n) Ss := measure_union_le _ _
    _ ≤ ENNReal.ofReal (averageFourthMomentBound (gaussianReal 0 1) positiveSquared /
          ((Fintype.card n : ℝ) ^ 2 * t ^ 4)) +
        ENNReal.ofReal (averageFourthMomentBound (gaussianReal 0 1) (fun x : ℝ => x ^ 2) /
          ((Fintype.card n : ℝ) ^ 2 * t ^ 4)) := add_le_add hp hs
    _ = _ := by
      rw [← ENNReal.ofReal_add
        (div_nonneg (averageFourthMomentBound_nonneg _ _) (by positivity))
        (div_nonneg (averageFourthMomentBound_nonneg _ _) (by positivity)), ← add_div]
      rfl

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Equality of the complete energy-fraction laws; input length cancels. -/
theorem vectorLaw_map_positiveEnergyFraction (x : n → ℝ) (hx : x ≠ 0) :
    (vectorLaw x).map positiveEnergyFraction = (gaussianVector n).map positiveEnergyFraction := by
  obtain ⟨i, _⟩ := Function.ne_iff.mp hx
  let _ : Nonempty n := ⟨i⟩
  have hn : 0 < ‖WithLp.toLp 2 x‖ := norm_pos_iff.mpr (by simpa using hx)
  have hm : Measurable (fun g : n → ℝ => ‖WithLp.toLp 2 x‖ • direction g) := by
    exact (continuous_id.const_smul ‖WithLp.toLp 2 x‖).measurable.comp measurable_direction
  rw [vectorLaw_eq_normalized_gaussian, Measure.map_map measurable_positiveEnergyFraction hm]
  congr 1
  funext g
  simp only [Function.comp_def, positiveEnergyFraction_smul _ hn, positiveEnergyFraction_direction]

theorem haar_positiveEnergyFraction_hasLaw (x : n → ℝ) (hx : x ≠ 0) :
    HasLaw (fun U : Group n => positiveEnergyFraction ((U : Matrix n n ℝ) *ᵥ x))
      ((gaussianVector n).map positiveEnergyFraction) (haar n) := by
  have hvec : HasLaw (fun U : Group n => (U : Matrix n n ℝ) *ᵥ x) (vectorLaw x) (haar n) :=
    ⟨(continuous_mulVec x).measurable.aemeasurable, rfl⟩
  have hf : HasLaw positiveEnergyFraction ((gaussianVector n).map positiveEnergyFraction) (vectorLaw x) :=
    ⟨measurable_positiveEnergyFraction.aemeasurable, vectorLaw_map_positiveEnergyFraction x hx⟩
  exact hf.fun_comp hvec

theorem haar_positiveEnergyFraction_deviation_le (x : n → ℝ) (hx : x ≠ 0)
    (ε : ℝ) (hε : 0 < ε) :
    (haar n) {U | ε ≤ |positiveEnergyFraction ((U : Matrix n n ℝ) *ᵥ x) - 1 / 2|} ≤
      ENNReal.ofReal (energyFourthMomentBound /
        ((Fintype.card n : ℝ) ^ 2 * energyDeviationThreshold ε ^ 4)) := by
  obtain ⟨i, _⟩ := Function.ne_iff.mp hx
  let _ : Nonempty n := ⟨i⟩
  have hN : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hg : HasLaw positiveEnergyFraction ((gaussianVector n).map positiveEnergyFraction) (gaussianVector n) :=
    ⟨measurable_positiveEnergyFraction.aemeasurable, rfl⟩
  have hm : MeasurableSet {a : ℝ | ε ≤ |a - 1 / 2|} :=
    measurableSet_le measurable_const (continuous_id.sub continuous_const).abs.measurable
  rw [(haar_positiveEnergyFraction_hasLaw x hx).measure_eq hm, ← hg.measure_eq hm]
  exact gaussian_positiveEnergyFraction_deviation_le hN ε hε

/-- The actual fraction of energy surviving a Haar ReLU gate converges almost
surely to one half for arbitrary coupling between linearly growing widths. -/
theorem ae_haar_positiveEnergyFraction_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {n : ℕ → Type*} [∀ k, Fintype (n k)] [∀ k, DecidableEq (n k)]
    (x : ∀ k, n k → ℝ) (hx : ∀ k, x k ≠ 0) (U : ∀ k, Ω → Group (n k))
    (hU : ∀ k, HasLaw (U k) (haar (n k)) μ) (δ : ℝ) (hδ : 0 < δ)
    (hdim : ∀ k : ℕ, δ * ((k : ℝ) + 1) ≤ (Fintype.card (n k) : ℝ)) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun k => positiveEnergyFraction ((U k ω : Matrix (n k) (n k) ℝ) *ᵥ x k))
      atTop (nhds (1 / 2 : ℝ)) := by
  have hlim : ∀ᵐ ω ∂μ, Tendsto
      (fun k => positiveEnergyFraction ((U k ω : Matrix (n k) (n k) ℝ) *ᵥ x k) - 1 / 2)
        atTop (nhds 0) := by
    apply ae_tendsto_zero_of_summable_deviations
    intro ε hε
    let t := energyDeviationThreshold ε
    have ht : 0 < t := energyDeviationThreshold_pos hε
    let C := energyFourthMomentBound
    have hC : 0 ≤ C := energyFourthMomentBound_nonneg
    let b := fun k : ℕ => (C / (δ ^ 2 * t ^ 4)) * (1 / ((k : ℝ) + 1) ^ 2)
    have hbnd (k : ℕ) : μ {ω | ε ≤
        |positiveEnergyFraction ((U k ω : Matrix (n k) (n k) ℝ) *ᵥ x k) - 1 / 2|} ≤
          ENNReal.ofReal (b k) := by
      have hm : MeasurableSet {V : Group (n k) | ε ≤
          |positiveEnergyFraction ((V : Matrix (n k) (n k) ℝ) *ᵥ x k) - 1 / 2|} :=
        measurableSet_le measurable_const ((show Measurable (fun a : ℝ => |a|) from
          continuous_id.abs.measurable).comp
          ((measurable_positiveEnergyFraction.comp (continuous_mulVec (x k)).measurable).sub
            measurable_const))
      rw [(hU k).measure_eq hm]
      apply (haar_positiveEnergyFraction_deviation_le (x k) (hx k) ε hε).trans
      apply ENNReal.ofReal_le_ofReal
      have hk : 0 < (k : ℝ) + 1 := by positivity
      have hs : δ ^ 2 * ((k : ℝ) + 1) ^ 2 ≤ (Fintype.card (n k) : ℝ) ^ 2 := by
        simpa [mul_pow] using pow_le_pow_left₀ (mul_pos hδ hk).le (hdim k) 2
      calc
        _ ≤ C / ((δ ^ 2 * ((k : ℝ) + 1) ^ 2) * t ^ 4) :=
          div_le_div_of_nonneg_left hC (by positivity)
            (mul_le_mul_of_nonneg_right hs (by positivity))
        _ = b k := by dsimp [b]; field_simp [hδ.ne', ht.ne', hk.ne']
    have hp := (Real.summable_one_div_nat_pow (p := 2)).mpr (by decide)
    have hs : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
      simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hp
    have hb : (∑' k, ENNReal.ofReal (b k)) < ∞ :=
      (hs.mul_left (C / (δ ^ 2 * t ^ 4))).tsum_ofReal_lt_top
    exact (lt_of_le_of_lt (ENNReal.tsum_le_tsum hbnd) hb).ne
  filter_upwards [hlim] with ω hω
  have hc : Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (nhds (1 / 2 : ℝ)) := tendsto_const_nhds
  have h := hω.add hc
  simpa only [sub_add_cancel, zero_add] using h

end FreeProbability.Orthogonal

import FreeProbability.RandomMatrix.HaarSignEnergy
import FreeProbability.Applications.ReLU.GateProjection

/-! # Actual one-layer ReLU forward energy and its almost-sure limit -/

namespace FreeProbability.ReLU

open Matrix MeasureTheory ProbabilityTheory Filter

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem gateProjection_mulVec (v : n → ℝ) :
    gateProjection v *ᵥ v = (fun i => max 0 (v i)) := by
  funext i
  by_cases hi : 0 < v i
  · simp [gateProjection, mulVec_diagonal, hi, max_eq_right hi.le]
  · simp [gateProjection, mulVec_diagonal, hi, max_eq_left (le_of_not_gt hi)]

theorem gateProjection_mulVec_norm_sq (v : n → ℝ) :
    ‖WithLp.toLp 2 (gateProjection v *ᵥ v)‖ ^ 2 = ∑ i, Orthogonal.positiveSquared (v i) := by
  rw [gateProjection_mulVec]
  simpa only [Orthogonal.positiveSquared] using
    EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 (fun i => max 0 (v i)))

noncomputable def gateEnergyFraction (v : n → ℝ) : ℝ :=
  ‖WithLp.toLp 2 (gateProjection v *ᵥ v)‖ ^ 2 / ‖WithLp.toLp 2 v‖ ^ 2

theorem gateEnergyFraction_eq_positiveEnergyFraction (v : n → ℝ) :
    gateEnergyFraction v = Orthogonal.positiveEnergyFraction v := by
  rw [gateEnergyFraction, gateProjection_mulVec_norm_sq, EuclideanSpace.real_norm_sq_eq]
  rfl

noncomputable def gateAmplitude (v : n → ℝ) : ℝ :=
  ‖WithLp.toLp 2 (gateProjection v *ᵥ v)‖ / ‖WithLp.toLp 2 v‖

theorem gateAmplitude_sq (v : n → ℝ) : gateAmplitude v ^ 2 = gateEnergyFraction v := by
  simp only [gateAmplitude, gateEnergyFraction, div_pow]

theorem sqrt_gateEnergyFraction (v : n → ℝ) : Real.sqrt (gateEnergyFraction v) = gateAmplitude v := by
  rw [← gateAmplitude_sq]
  exact Real.sqrt_sq (div_nonneg (norm_nonneg _) (norm_nonneg _))

theorem ae_haar_gateEnergyFraction_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {n : ℕ → Type*} [∀ k, Fintype (n k)] [∀ k, DecidableEq (n k)]
    (x : ∀ k, n k → ℝ) (hx : ∀ k, x k ≠ 0) (U : ∀ k, Ω → Orthogonal.Group (n k))
    (hU : ∀ k, HasLaw (U k) (Orthogonal.haar (n k)) μ) (δ : ℝ) (hδ : 0 < δ)
    (hdim : ∀ k : ℕ, δ * ((k : ℝ) + 1) ≤ (Fintype.card (n k) : ℝ)) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun k => gateEnergyFraction ((U k ω : Matrix (n k) (n k) ℝ) *ᵥ x k))
        atTop (nhds (1 / 2 : ℝ)) := by
  simpa only [gateEnergyFraction_eq_positiveEnergyFraction] using
    Orthogonal.ae_haar_positiveEnergyFraction_tendsto μ x hx U hU δ hδ hdim

theorem ae_haar_gateAmplitude_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {n : ℕ → Type*} [∀ k, Fintype (n k)] [∀ k, DecidableEq (n k)]
    (x : ∀ k, n k → ℝ) (hx : ∀ k, x k ≠ 0) (U : ∀ k, Ω → Orthogonal.Group (n k))
    (hU : ∀ k, HasLaw (U k) (Orthogonal.haar (n k)) μ) (δ : ℝ) (hδ : 0 < δ)
    (hdim : ∀ k : ℕ, δ * ((k : ℝ) + 1) ≤ (Fintype.card (n k) : ℝ)) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun k => gateAmplitude ((U k ω : Matrix (n k) (n k) ℝ) *ᵥ x k))
        atTop (nhds (Real.sqrt (1 / 2))) := by
  filter_upwards [ae_haar_gateEnergyFraction_tendsto μ x hx U hU δ hδ hdim] with ω hω
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hω
  simpa only [Function.comp_def, sqrt_gateEnergyFraction] using h

theorem ae_haar_gateProjection_mulVec_eventually_ne_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {n : ℕ → Type*} [∀ k, Fintype (n k)] [∀ k, DecidableEq (n k)]
    (x : ∀ k, n k → ℝ) (hx : ∀ k, x k ≠ 0) (U : ∀ k, Ω → Orthogonal.Group (n k))
    (hU : ∀ k, HasLaw (U k) (Orthogonal.haar (n k)) μ) (δ : ℝ) (hδ : 0 < δ)
    (hdim : ∀ k : ℕ, δ * ((k : ℝ) + 1) ≤ (Fintype.card (n k) : ℝ)) :
    ∀ᵐ ω ∂μ, ∀ᶠ k in atTop,
      gateProjection ((U k ω : Matrix (n k) (n k) ℝ) *ᵥ x k) *ᵥ
        ((U k ω : Matrix (n k) (n k) ℝ) *ᵥ x k) ≠ 0 := by
  filter_upwards [ae_haar_gateEnergyFraction_tendsto μ x hx U hU δ hδ hdim] with ω hω
  have hp := hω.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hp] with k hk
  intro hz
  have he : gateEnergyFraction ((U k ω : Matrix (n k) (n k) ℝ) *ᵥ x k) = 0 := by
    simp [gateEnergyFraction, hz]
  change 0 < gateEnergyFraction ((U k ω : Matrix (n k) (n k) ℝ) *ᵥ x k) at hk
  rw [he] at hk
  exact (lt_irrefl 0) hk

end FreeProbability.ReLU

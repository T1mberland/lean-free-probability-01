import FreeProbability.OperatorValued.MatrixDysonContraction
import Mathlib.Analysis.Analytic.Uniqueness

/-! # Uniqueness of decaying analytic matrix Dyson branches

The matrix norm is the submultiplicative row operator norm. The result concerns
analytic branches on connected open domains; it does not claim pointwise
uniqueness among all matrices with negative imaginary part at a fixed argument.
-/

noncomputable section
open scoped Classical Topology Matrix.Norms.Operator
namespace FreeProbability

variable {I n : Type*} [Fintype I] [Fintype n] [DecidableEq n]

/-- One small-norm point determines an analytic Dyson branch throughout a
connected open domain, by local contraction and the analytic identity principle. -/
theorem matrixDyson_analytic_unique_of_small_point (C : I → Matrix n n ℂ)
    (B F G : ℂ → Matrix n n ℂ) (U : Set ℂ) (hU : IsOpen U) (hconn : IsPreconnected U)
    (hF : AnalyticOnNhd ℂ F U) (hG : AnalyticOnNhd ℂ G U)
    (hFD : ∀ z ∈ U, (B z - matrixCovariance C (F z)) * F z = 1)
    (hGD : ∀ z ∈ U, (B z - matrixCovariance C (G z)) * G z = 1)
    (z₀ : ℂ) (hz₀ : z₀ ∈ U)
    (hsmall : ‖F z₀‖ * (∑ i, ‖C i‖ ^ 2) * ‖G z₀‖ < 1) : Set.EqOn F G U := by
  have hc : ContinuousAt (fun z => ‖F z‖ * (∑ i, ‖C i‖ ^ 2) * ‖G z‖) z₀ :=
    ((hF z₀ hz₀).continuousAt.norm.mul continuousAt_const).mul (hG z₀ hz₀).continuousAt.norm
  have hs := hc.eventually (gt_mem_nhds hsmall)
  have heq : F =ᶠ[𝓝 z₀] G := by
    filter_upwards [hs, hU.mem_nhds hz₀] with z hz hu
    exact matrixDyson_unique_of_norm_small C (B z) (F z) (G z) (hFD z hu) (hGD z hu) hz
  exact hF.eqOn_of_preconnected_of_eventuallyEq hG hconn hz₀ heq

/-- Two analytic matrix Dyson branches decaying at infinity within the same
unbounded connected open domain coincide throughout that domain. -/
theorem matrixDyson_analytic_unique_of_decay (C : I → Matrix n n ℂ)
    (B F G : ℂ → Matrix n n ℂ) (U : Set ℂ) (hU : IsOpen U) (hconn : IsPreconnected U)
    (hunbounded : ¬ Bornology.IsBounded U)
    (hF : AnalyticOnNhd ℂ F U) (hG : AnalyticOnNhd ℂ G U)
    (hFD : ∀ z ∈ U, (B z - matrixCovariance C (F z)) * F z = 1)
    (hGD : ∀ z ∈ U, (B z - matrixCovariance C (G z)) * G z = 1)
    (hFzero : Filter.Tendsto F (Bornology.cobounded ℂ ⊓ Filter.principal U) (𝓝 0))
    (hGzero : Filter.Tendsto G (Bornology.cobounded ℂ ⊓ Filter.principal U) (𝓝 0)) :
    Set.EqOn F G U := by
  let L := Bornology.cobounded ℂ ⊓ Filter.principal U
  have hfreq : ∃ᶠ z in Bornology.cobounded ℂ, z ∈ U := hunbounded
  have : L.NeBot := Filter.frequently_mem_iff_neBot.mp hfreq
  have hc : Filter.Tendsto (fun z => ‖F z‖ * (∑ i, ‖C i‖ ^ 2) * ‖G z‖) L (𝓝 0) := by
    simpa using (hFzero.norm.mul tendsto_const_nhds).mul hGzero.norm
  have hs : ∀ᶠ z in L, ‖F z‖ * (∑ i, ‖C i‖ ^ 2) * ‖G z‖ < 1 :=
    hc.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  have hu : ∀ᶠ z in L, z ∈ U :=
    (Filter.eventually_mem_principal U : ∀ᶠ z in Filter.principal U, z ∈ U).filter_mono inf_le_right
  obtain ⟨z, hz, hzu⟩ := (hs.and hu).exists
  exact matrixDyson_analytic_unique_of_small_point C B F G U hU hconn hF hG hFD hGD z hzu hz

omit [Fintype n] in
/-- The usual normalization at infinity implies decay within an arbitrary domain. -/
theorem matrixBranch_decay_of_normalized (F : ℂ → Matrix n n ℂ) (U : Set ℂ)
    (hF : Filter.Tendsto (fun z => z • F z)
      (Bornology.cobounded ℂ ⊓ Filter.principal U) (𝓝 (1 : Matrix n n ℂ))) :
    Filter.Tendsto F (Bornology.cobounded ℂ ⊓ Filter.principal U) (𝓝 0) := by
  have hi : Filter.Tendsto (fun z : ℂ => z⁻¹)
      (Bornology.cobounded ℂ ⊓ Filter.principal U) (𝓝 0) :=
    (Filter.tendsto_inv₀_cobounded (α := ℂ)).mono_left inf_le_left
  have hs := hi.smul hF
  have heq : (fun z : ℂ => z⁻¹ • (z • F z)) =ᶠ[Bornology.cobounded ℂ ⊓ Filter.principal U] F := by
    have hz : ∀ᶠ z : ℂ in Bornology.cobounded ℂ ⊓ Filter.principal U, z ≠ 0 :=
      by
        have hz₀ : ∀ᶠ z : ℂ in Bornology.cobounded ℂ, z ≠ 0 :=
          Bornology.isBounded_singleton
        exact hz₀.filter_mono inf_le_left
    filter_upwards [hz] with z hz
    rw [smul_smul, inv_mul_cancel₀ hz, one_smul]
  simpa using hs.congr' heq

/-- Normalized analytic matrix Dyson branches coincide on every unbounded
connected open domain. Normalization is within the domain at infinity. -/
theorem matrixDyson_analytic_unique_of_normalized (C : I → Matrix n n ℂ)
    (B F G : ℂ → Matrix n n ℂ) (U : Set ℂ) (hU : IsOpen U) (hconn : IsPreconnected U)
    (hunbounded : ¬ Bornology.IsBounded U)
    (hF : AnalyticOnNhd ℂ F U) (hG : AnalyticOnNhd ℂ G U)
    (hFD : ∀ z ∈ U, (B z - matrixCovariance C (F z)) * F z = 1)
    (hGD : ∀ z ∈ U, (B z - matrixCovariance C (G z)) * G z = 1)
    (hFone : Filter.Tendsto (fun z => z • F z)
      (Bornology.cobounded ℂ ⊓ Filter.principal U) (𝓝 (1 : Matrix n n ℂ)))
    (hGone : Filter.Tendsto (fun z => z • G z)
      (Bornology.cobounded ℂ ⊓ Filter.principal U) (𝓝 (1 : Matrix n n ℂ))) :
    Set.EqOn F G U :=
  matrixDyson_analytic_unique_of_decay C B F G U hU hconn hunbounded hF hG hFD hGD
    (matrixBranch_decay_of_normalized F U hFone) (matrixBranch_decay_of_normalized G U hGone)

end FreeProbability

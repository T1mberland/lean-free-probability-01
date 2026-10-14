import FreeProbability.RandomMatrix.OrthogonalMultiTraceProbabilityRandomInputsMarginals
import Mathlib.Probability.Independence.Integration

/-! # Genuine colored entry integration for independent orthogonal Haar matrices -/

noncomputable section
open scoped Classical Topology
namespace FreeProbability.Orthogonal
open Matrix MeasureTheory Filter ProbabilityTheory
variable {Ω I n : Type*} [MeasurableSpace Ω] [Fintype I] [Fintype n] [DecidableEq n]
variable (μ : Measure Ω) (X : I → Ω → Group n)

/-- A genuine colored product of actual real orthogonal matrix entries. -/
def coloredEntryMonomial {k : I → ℕ} (i j : ∀ c, Fin (k c) → n) (ω : Ω) : ℝ :=
  ∏ c, entryMonomial (i c) (j c) (X c ω)

/-- The actual colored Bochner entry integral. -/
def coloredEntryIntegral {k : I → ℕ} (i j : ∀ c, Fin (k c) → n) : ℝ :=
  ∫ ω, coloredEntryMonomial X i j ω ∂μ

/-- True finite probabilistic independence and actual Haar marginals imply
the actual joint product Haar law, including an empty color index. -/
theorem independent_coloredHaar_measurePreserving (hi : iIndepFun X μ)
    (hX : ∀ c, MeasurePreserving (X c) μ (haar n)) :
    MeasurePreserving (fun ω c => X c ω) μ (Measure.pi (fun _ : I => haar n)) := by
  refine ⟨measurable_pi_iff.mpr (fun c => (hX c).measurable), ?_⟩
  rw [hi.map_fun_eq_pi_map (fun c => (hX c).measurable.aemeasurable)]
  have he : (fun c => μ.map (X c)) = (fun _ : I => haar n) := funext (fun c => (hX c).map_eq)
  rw [he]

/-- Actual colored monomials are integrable, derived from their joint Haar law. -/
theorem integrable_coloredEntryMonomial {k : I → ℕ} (i j : ∀ c, Fin (k c) → n)
    (hi : iIndepFun X μ) (hX : ∀ c, MeasurePreserving (X c) μ (haar n)) :
    Integrable (coloredEntryMonomial X i j) μ := by
  have hc : Continuous (fun U : I → Group n => ∏ c, entryMonomial (i c) (j c) (U c)) := by
    apply continuous_finsetProd
    intro c _
    exact (continuous_entryMonomial (i c) (j c)).comp (continuous_apply c)
  have hint : Integrable (fun U : I → Group n => ∏ c, entryMonomial (i c) (j c) (U c))
      (Measure.pi (fun _ : I => haar n)) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact (independent_coloredHaar_measurePreserving μ X hi hX).integrable_comp_of_integrable hint

/-- The actual colored integral factors into actual one-color Haar entry
moments, rather than assuming an integration or factorization formula. -/
theorem coloredEntryIntegral_eq_product {k : I → ℕ} (i j : ∀ c, Fin (k c) → n)
    (hi : iIndepFun X μ) (hX : ∀ c, MeasurePreserving (X c) μ (haar n)) :
    coloredEntryIntegral μ X i j = ∏ c, entryMoment (i c) (j c) := by
  have hm (c : I) : AEStronglyMeasurable (entryMonomial (i c) (j c)) (μ.map (X c)) := by
    rw [(hX c).map_eq]
    exact (integrable_entryMonomial (i c) (j c)).1
  have he (c : I) : (∫ ω, entryMonomial (i c) (j c) (X c ω) ∂μ) = entryMoment (i c) (j c) := by
    have ht := (integral_map (hX c).measurable.aemeasurable (hm c)).symm
    simpa only [(hX c).map_eq, entryMoment] using ht
  unfold coloredEntryIntegral coloredEntryMonomial
  rw [hi.integral_fun_prod_comp (fun c => (hX c).measurable.aemeasurable) hm]
  simp_rw [he]

/-- A zero-degree color contributes the genuine scalar moment one. -/
theorem coloredEntryIntegral_all_zero (i j : ∀ _c : I, Fin 0 → n)
    (hi : iIndepFun X μ) (hX : ∀ c, MeasurePreserving (X c) μ (haar n)) :
    coloredEntryIntegral μ X i j = 1 := by
  rw [coloredEntryIntegral_eq_product μ X i j hi hX]
  simp

/-- Any odd-degree color kills the actual full colored integral. -/
theorem coloredEntryIntegral_eq_zero_of_odd {k : I → ℕ} (i j : ∀ c, Fin (k c) → n)
    (hi : iIndepFun X μ) (hX : ∀ c, MeasurePreserving (X c) μ (haar n))
    (c : I) (hc : Odd (k c)) : coloredEntryIntegral μ X i j = 0 := by
  rw [coloredEntryIntegral_eq_product μ X i j hi hX]
  exact Finset.prod_eq_zero (Finset.mem_univ c) (entryMoment_eq_zero_of_odd (i c) (j c) hc)

end FreeProbability.Orthogonal

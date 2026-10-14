import FreeProbability.RandomMatrix.OrthogonalVectorLaw
import Mathlib.MeasureTheory.Integral.Prod

/-! # Uniqueness of orthogonally invariant probability on a Euclidean sphere -/

namespace FreeProbability.Orthogonal

open Matrix MeasureTheory

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An orthogonally invariant probability supported on one fixed sphere equals
the actual Haar image law on that sphere. This also covers the radius-zero sphere. -/
theorem eq_vectorLaw_of_invariant_sphere (μ : Measure (n → ℝ)) [IsProbabilityMeasure μ]
    (x : n → ℝ) (hsphere : ∀ᵐ y ∂μ, ‖WithLp.toLp 2 y‖ = ‖WithLp.toLp 2 x‖)
    (hinv : ∀ V : Group n, μ.map (fun y => (V : Matrix n n ℝ) *ᵥ y) = μ) :
    μ = vectorLaw x := by
  apply Measure.ext
  intro E hE
  let f : (n → ℝ) → ℝ := E.indicator (fun _ => 1)
  let g : Group n × (n → ℝ) → ℝ := fun p => f ((p.1 : Matrix n n ℝ) *ᵥ p.2)
  have hf : Measurable f := measurable_const.indicator hE
  have hg : Measurable g := hf.comp continuous_action.measurable
  have hi : Integrable g ((haar n).prod μ) := by
    apply Integrable.of_bound hg.aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro p
    by_cases hp : (p.1 : Matrix n n ℝ) *ᵥ p.2 ∈ E <;> simp [g, f, hp]
  have hμ : (∫ y, f y ∂μ) = μ.real E := integral_indicator_one hE
  have hν : (∫ y, f y ∂vectorLaw x) = (vectorLaw x).real E := integral_indicator_one hE
  have hleft (V : Group n) : (∫ y, g (V, y) ∂μ) = μ.real E := by
    have hm : Measurable (fun y => (V : Matrix n n ℝ) *ᵥ y) :=
      (continuous_action.comp (continuous_const.prodMk continuous_id)).measurable
    have h := integral_map (μ := μ) hm.aemeasurable hf.aestronglyMeasurable
    change (∫ y, f y ∂μ.map (fun y => (V : Matrix n n ℝ) *ᵥ y)) =
      ∫ y, g (V, y) ∂μ at h
    rw [hinv V, hμ] at h
    exact h.symm
  have hright : (fun y => ∫ V : Group n, g (V, y) ∂haar n) =ᵐ[μ]
      (fun _ => (vectorLaw x).real E) := by
    filter_upwards [hsphere] with y hy
    have h := integral_map (μ := haar n) (continuous_mulVec y).aemeasurable hf.aestronglyMeasurable
    change (∫ z, f z ∂vectorLaw y) = ∫ V : Group n, g (V, y) ∂haar n at h
    rw [vectorLaw_eq_of_norm_eq y x hy, hν] at h
    exact h.symm
  have hF := (integral_prod g hi).symm.trans (integral_prod_symm g hi)
  simp_rw [hleft] at hF
  rw [integral_congr_ae hright] at hF
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hF
  have h := congrArg ENNReal.ofReal hF
  rw [ofReal_measureReal (μ := μ) (s := E), ofReal_measureReal (μ := vectorLaw x) (s := E)] at h
  exact h

end FreeProbability.Orthogonal

import FreeProbability.Analytic.SpectralMeasureUniqueness
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# From bounded algebraic moment convergence to actual spectral weak convergence

The source C-star algebras may vary and the filter is arbitrary. Approximation
is on a genuine common compact spectral set, not an exterior power series.
-/

noncomputable section
open scoped Classical Topology
open MeasureTheory

namespace FreeProbability

variable {ι A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {B : ι → Type*} [∀ i, CStarAlgebra (B i)] [∀ i, PartialOrder (B i)] [∀ i, StarOrderedRing (B i)]
  (φ : StarProbabilitySpace A) (ψ : ∀ i, StarProbabilitySpace (B i))

omit [PartialOrder A] [StarOrderedRing A] [∀ i, PartialOrder (B i)] [∀ i, StarOrderedRing (B i)] in
/-- Power-moment convergence gives every finite real polynomial moment, with varying source algebras. -/
theorem tendsto_real_polynomial_expectation_of_power_moments (a : A) (b : ∀ i, B i) (l : Filter ι)
    (hm : ∀ n : ℕ, Filter.Tendsto (fun i => (ψ i).expectation (b i ^ n)) l (𝓝 (φ.expectation (a ^ n))))
    (p : Polynomial ℝ) :
    Filter.Tendsto (fun i => (ψ i).expectation (Polynomial.aeval (b i) p)) l
      (𝓝 (φ.expectation (Polynomial.aeval a p))) := by
  let F : ∀ i, B i →ₗ[ℝ] ℂ := fun i => (ψ i).expectation.restrictScalars ℝ
  let G := φ.expectation.restrictScalars ℝ
  change Filter.Tendsto (fun i => F i (Polynomial.aeval (b i) p)) l (𝓝 (G (Polynomial.aeval a p)))
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | monomial n c =>
    simp only [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one,
      Algebra.smul_mul_assoc, one_mul, map_smul]
    exact (hm n).const_smul c

/-- Uniform approximation on an actual spectral superset controls expectation errors. -/
theorem expectation_cfc_polynomial_error_bound {a : A} (ha : IsSelfAdjoint a)
    {K : Set ℝ} [CompactSpace K] (hK : spectrum ℝ a ⊆ K) (f : C(ℝ, ℝ)) (p : Polynomial ℝ) :
    ‖φ.expectation (cfc f a) - φ.expectation (Polynomial.aeval a p)‖ ≤
      ‖f.comp ⟨Subtype.val, continuous_subtype_val⟩ - Polynomial.toContinuousMapOnAlgHom K p‖ := by
  rw [← cfc_polynomial p a ha, ← map_sub,
    ← cfc_sub f p.eval a f.continuous.continuousOn p.continuous.continuousOn]
  apply (φ.expectation_norm_le _).trans
  apply norm_cfc_le (norm_nonneg _)
  intro x hx
  exact ContinuousMap.norm_coe_le_norm
    (f.comp ⟨Subtype.val, continuous_subtype_val⟩ - Polynomial.toContinuousMapOnAlgHom K p) ⟨x, hK hx⟩

/-- Moment convergence and eventual common compact spectra give every continuous real CFC limit. -/
theorem tendsto_real_cfc_of_power_moments (a : A) (ha : IsSelfAdjoint a)
    (b : ∀ i, B i) (hb : ∀ i, IsSelfAdjoint (b i)) (l : Filter ι)
    (hm : ∀ n : ℕ, Filter.Tendsto (fun i => (ψ i).expectation (b i ^ n)) l (𝓝 (φ.expectation (a ^ n))))
    (K : Set ℝ) (hcompact : IsCompact K) (hA : spectrum ℝ a ⊆ K)
    (hB : ∀ᶠ i in l, spectrum ℝ (b i) ⊆ K) (f : C(ℝ, ℝ)) :
    Filter.Tendsto (fun i => (ψ i).expectation (cfc f (b i))) l (𝓝 (φ.expectation (cfc f a))) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hcompact
  let g : C(K, ℝ) := f.comp ⟨Subtype.val, continuous_subtype_val⟩
  have hg : g ∈ closure (polynomialFunctions K : Set C(K, ℝ)) := by
    change g ∈ (polynomialFunctions K).topologicalClosure
    rw [polynomialFunctions.topologicalClosure]
    trivial
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨q, hq, hdist⟩ := Metric.mem_closure_iff.mp hg (ε / 3) (by positivity)
  rw [polynomialFunctions_coe] at hq
  obtain ⟨p, rfl⟩ := hq
  have hnear := Metric.tendsto_nhds.mp
    (tendsto_real_polynomial_expectation_of_power_moments φ ψ a b l hm p) (ε / 3) (by positivity)
  have htarget : ‖φ.expectation (cfc f a) - φ.expectation (Polynomial.aeval a p)‖ < ε / 3 := by
    apply lt_of_le_of_lt (expectation_cfc_polynomial_error_bound φ ha hA f p)
    exact (dist_eq_norm g _).symm ▸ hdist
  filter_upwards [hB, hnear] with i hi him
  have hsource : ‖(ψ i).expectation (cfc f (b i)) - (ψ i).expectation (Polynomial.aeval (b i) p)‖ < ε / 3 := by
    apply lt_of_le_of_lt (expectation_cfc_polynomial_error_bound (ψ i) (hb i) hi f p)
    exact (dist_eq_norm g _).symm ▸ hdist
  rw [dist_eq_norm] at him ⊢
  have ht := norm_sub_le_norm_sub_add_norm_sub
    ((ψ i).expectation (cfc f (b i))) ((ψ i).expectation (Polynomial.aeval (b i) p))
    (φ.expectation (cfc f a))
  have ht' := norm_sub_le_norm_sub_add_norm_sub
    ((ψ i).expectation (Polynomial.aeval (b i) p)) (φ.expectation (Polynomial.aeval a p))
    (φ.expectation (cfc f a))
  rw [norm_sub_rev (φ.expectation (Polynomial.aeval a p)) (φ.expectation (cfc f a))] at ht'
  linarith

/-- An eventual common operator-norm bound suffices for all continuous real CFC expectations. -/
theorem tendsto_real_cfc_of_bounded_power_moments (a : A) (ha : IsSelfAdjoint a)
    (b : ∀ i, B i) (hb : ∀ i, IsSelfAdjoint (b i)) (l : Filter ι)
    (hm : ∀ n : ℕ, Filter.Tendsto (fun i => (ψ i).expectation (b i ^ n)) l (𝓝 (φ.expectation (a ^ n))))
    (R : ℝ) (hbound : ∀ᶠ i in l, ‖b i‖ ≤ R) (f : C(ℝ, ℝ)) :
    Filter.Tendsto (fun i => (ψ i).expectation (cfc f (b i))) l (𝓝 (φ.expectation (cfc f a))) := by
  let _ : Nontrivial A := φ.toProbabilitySpace.nontrivial
  let K := Metric.closedBall (0 : ℝ) (max R ‖a‖)
  have hA : spectrum ℝ a ⊆ K := by
    intro x hx
    change dist x 0 ≤ max R ‖a‖
    rw [dist_zero_right]
    exact (spectrum.norm_le_norm_of_mem hx).trans (le_max_right _ _)
  have hB : ∀ᶠ i in l, spectrum ℝ (b i) ⊆ K := by
    filter_upwards [hbound] with i hi x hx
    let _ : Nontrivial (B i) := (ψ i).toProbabilitySpace.nontrivial
    change dist x 0 ≤ max R ‖a‖
    rw [dist_zero_right]
    exact (spectrum.norm_le_norm_of_mem hx).trans (hi.trans (le_max_left _ _))
  exact tendsto_real_cfc_of_power_moments φ ψ a ha b hb l hm K (isCompact_closedBall _ _) hA hB f

/-- All continuous real test integrals of the actual spectral measures converge under a norm bound. -/
theorem tendsto_spectralIntegral_of_bounded_power_moments (a : A) (ha : IsSelfAdjoint a)
    (b : ∀ i, B i) (hb : ∀ i, IsSelfAdjoint (b i)) (l : Filter ι)
    (hm : ∀ n : ℕ, Filter.Tendsto (fun i => (ψ i).expectation (b i ^ n)) l (𝓝 (φ.expectation (a ^ n))))
    (R : ℝ) (hbound : ∀ᶠ i in l, ‖b i‖ ≤ R) (f : C(ℝ, ℝ)) :
    Filter.Tendsto (fun i => ∫ x, f x ∂spectralMeasure (ψ i) (hb i)) l
      (𝓝 (∫ x, f x ∂spectralMeasure φ ha)) := by
  have ht := tendsto_real_cfc_of_bounded_power_moments φ ψ a ha b hb l hm R hbound f
  have hr := (Complex.continuous_re.tendsto (φ.expectation (cfc f a))).comp ht
  have he i := expectation_cfc_eq_integral (ψ i) (hb i) f f.continuous
  have hea := expectation_cfc_eq_integral φ ha f f.continuous
  simpa only [he, hea, Complex.ofReal_re, Function.comp_def] using hr

/-- The actual spectral probability law, packaged with the standard topology of weak convergence. -/
def spectralProbabilityMeasure {a : A} (ha : IsSelfAdjoint a) : ProbabilityMeasure ℝ :=
  ⟨spectralMeasure φ ha, inferInstance⟩

/-- Genuine weak convergence of actual spectral probability laws from bounded algebraic moments. -/
theorem tendsto_spectralProbabilityMeasure_of_bounded_power_moments (a : A) (ha : IsSelfAdjoint a)
    (b : ∀ i, B i) (hb : ∀ i, IsSelfAdjoint (b i)) (l : Filter ι)
    (hm : ∀ n : ℕ, Filter.Tendsto (fun i => (ψ i).expectation (b i ^ n)) l (𝓝 (φ.expectation (a ^ n))))
    (R : ℝ) (hbound : ∀ᶠ i in l, ‖b i‖ ≤ R) :
    Filter.Tendsto (fun i => spectralProbabilityMeasure (ψ i) (hb i)) l
      (𝓝 (spectralProbabilityMeasure φ ha)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  exact tendsto_spectralIntegral_of_bounded_power_moments φ ψ a ha b hb l hm R hbound
    ⟨f, f.continuous⟩

end FreeProbability

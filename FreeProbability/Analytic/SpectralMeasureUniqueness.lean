import FreeProbability.Analytic.SpectralMeasureMoments
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-! # Actual bounded spectral probability laws are determined by all power moments -/

noncomputable section
open scoped Classical CompactlySupported
open MeasureTheory

namespace FreeProbability

variable {A D : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  (φ : StarProbabilitySpace A) (ψ : StarProbabilitySpace D)
  {a : A} {b : D} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D] in
/-- Equal complex power moments also determine every real-coefficient polynomial expectation. -/
theorem real_polynomial_expectation_eq_of_power_moments
    (hm : ∀ n : ℕ, φ.expectation (a ^ n) = ψ.expectation (b ^ n)) (p : Polynomial ℝ) :
    φ.expectation (Polynomial.aeval a p) = ψ.expectation (Polynomial.aeval b p) := by
  let F := φ.expectation.restrictScalars ℝ
  let G := ψ.expectation.restrictScalars ℝ
  change F (Polynomial.aeval a p) = G (Polynomial.aeval b p)
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial n c =>
    simp only [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one,
      Algebra.smul_mul_assoc, one_mul, map_smul]
    exact congrArg (fun z : ℂ => c • z) (hm n)

omit [PartialOrder A] [StarOrderedRing A] in
/-- The genuine superset functional calculus sends each real polynomial to actual evaluation. -/
theorem cfcHomSuperset_polynomial {K : Set ℝ} (hK : spectrum ℝ a ⊆ K) (p : Polynomial ℝ) :
    cfcHomSuperset ha hK (Polynomial.toContinuousMapOnAlgHom K p) = Polynomial.aeval a p := by
  have he : (cfcHomSuperset ha hK).toAlgHom.comp (Polynomial.toContinuousMapOnAlgHom K) =
      Polynomial.aeval a := by
    apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, Polynomial.aeval_X, Polynomial.toContinuousMapOnAlgHom_apply]
    change cfcHomSuperset ha hK (Polynomial.X.toContinuousMapOn K) = a
    rw [Polynomial.toContinuousMapOn_X_eq_restrict_id, cfcHomSuperset_id]
  exact congrArg (fun f : Polynomial ℝ →ₐ[ℝ] A => f p) he

/-- Equal power moments imply equal expectations of every real continuous spectral function. -/
theorem real_cfc_expectation_eq_of_power_moments (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (hm : ∀ n : ℕ, φ.expectation (a ^ n) = ψ.expectation (b ^ n)) (f : C(ℝ, ℝ)) :
    φ.expectation (cfc f a) = ψ.expectation (cfc f b) := by
  let K := spectrum ℝ a ∪ spectrum ℝ b
  have hK : IsCompact K := (ContinuousFunctionalCalculus.isCompact_spectrum a).union
    (ContinuousFunctionalCalculus.isCompact_spectrum b)
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hA : spectrum ℝ a ⊆ K := Set.subset_union_left
  have hB : spectrum ℝ b ⊆ K := Set.subset_union_right
  let F : C(K, ℝ) → ℂ := fun g => φ.expectation (cfcHomSuperset ha hA g)
  let G : C(K, ℝ) → ℂ := fun g => ψ.expectation (cfcHomSuperset hb hB g)
  have hF : Continuous F := φ.continuous_expectation.comp (cfcHomSuperset_continuous ha hA)
  have hG : Continuous G := ψ.continuous_expectation.comp (cfcHomSuperset_continuous hb hB)
  have hp : ∀ g ∈ polynomialFunctions K, F g = G g := by
    intro g hg
    rw [← SetLike.mem_coe, polynomialFunctions_coe] at hg
    obtain ⟨p, rfl⟩ := hg
    change φ.expectation (cfcHomSuperset ha hA _) = ψ.expectation (cfcHomSuperset hb hB _)
    rw [cfcHomSuperset_polynomial ha hA, cfcHomSuperset_polynomial hb hB]
    exact real_polynomial_expectation_eq_of_power_moments φ ψ hm p
  have hc : closure (polynomialFunctions K : Set C(K, ℝ)) ⊆ {g | F g = G g} :=
    closure_minimal hp (isClosed_eq hF hG)
  have he (g : C(K, ℝ)) : F g = G g := by
    apply hc
    change g ∈ (polynomialFunctions K).topologicalClosure
    rw [polynomialFunctions.topologicalClosure]
    trivial
  let g : C(K, ℝ) := f.comp ⟨Subtype.val, continuous_subtype_val⟩
  have hg := he g
  have hea : cfcHomSuperset ha hA g = cfc f a := by
    rw [cfc_apply f a ha f.continuous.continuousOn]
    rfl
  have heb : cfcHomSuperset hb hB g = cfc f b := by
    rw [cfc_apply f b hb f.continuous.continuousOn]
    rfl
  simpa only [F, G, hea, heb] using hg

/-- Actual spectral measures of bounded self-adjoint realizations are determined by power moments. -/
theorem spectralMeasure_eq_of_power_moments
    (hm : ∀ n : ℕ, φ.expectation (a ^ n) = ψ.expectation (b ^ n)) :
    spectralMeasure φ ha = spectralMeasure ψ hb := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have he := real_cfc_expectation_eq_of_power_moments φ ψ ha hb hm f.toContinuousMap
  rw [expectation_cfc_eq_integral φ ha _ f.continuous,
    expectation_cfc_eq_integral ψ hb _ f.continuous] at he
  exact Complex.ofReal_injective he

/-- Exact equivalence between equality of actual bounded spectral laws and all algebraic moments. -/
theorem spectralMeasure_eq_iff_power_moments :
    spectralMeasure φ ha = spectralMeasure ψ hb ↔
      ∀ n : ℕ, φ.expectation (a ^ n) = ψ.expectation (b ^ n) := by
  constructor
  · intro h n
    rw [spectralMeasure_power_moment φ ha, spectralMeasure_power_moment ψ hb, h]
  · exact spectralMeasure_eq_of_power_moments φ ψ ha hb

end FreeProbability

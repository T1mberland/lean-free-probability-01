import FreeProbability.Algebraic.CumulantAdditivity
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Formal R-transforms

The coefficient of degree `n` is the free cumulant of order `n + 1`.
These are formal power-series identities; no convergence radius or analytic
inverse-transform identification is asserted here.
-/

namespace FreeProbability

variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]

/-- The R-transform as a formal series of free cumulants. -/
noncomputable def formalRTransform (φ : ProbabilitySpace 𝕜 A) (a : A) : PowerSeries 𝕜 :=
  PowerSeries.mk (fun n => cumulant φ (List.replicate (n + 1) a))

@[simp] theorem formalRTransform_coeff (φ : ProbabilitySpace 𝕜 A) (a : A) (n : ℕ) :
    PowerSeries.coeff n (formalRTransform φ a) = cumulant φ (List.replicate (n + 1) a) :=
  PowerSeries.coeff_mk _ _

/-- The constant coefficient is the expectation. -/
@[simp] theorem formalRTransform_constantCoeff (φ : ProbabilitySpace 𝕜 A) (a : A) :
    PowerSeries.constantCoeff (formalRTransform φ a) = φ.expectation a := by
  simp [PowerSeries.constantCoeff_mk, formalRTransform, cumulant, freeCumulant_singleton]

/-- Formal R-transforms add across an arbitrary finite free family. -/
theorem FreelyIndependent.formalRTransform_sum {I : Type*} [Fintype I]
    {φ : ProbabilitySpace 𝕜 A} {B : I → Subalgebra 𝕜 A}
    (hfree : FreelyIndependent φ B) (a : I → A) (ha : ∀ i, a i ∈ B i) :
    formalRTransform φ (∑ i, a i) = ∑ i, formalRTransform φ (a i) := by
  ext n
  simp only [formalRTransform_coeff, map_sum]
  exact hfree.cumulant_replicate_sum a ha (n + 1)

/-- Simultaneous scalar homogeneity of each univariate cumulant. -/
theorem cumulant_replicate_smul (φ : ProbabilitySpace 𝕜 A) (a : A) (c : 𝕜) (n : ℕ) :
    cumulant φ (List.replicate n (c • a)) = c ^ n * cumulant φ (List.replicate n a) := by
  have h := (cumulantMultilinear φ n).map_smul_univ (fun _ => c) (fun _ => a)
  simpa only [← cumulant_ofFn, List.ofFn_const, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul] using h

/-- Formal scaling law: `R_(c a)(z) = c R_a(c z)`. -/
theorem formalRTransform_smul (φ : ProbabilitySpace 𝕜 A) (a : A) (c : 𝕜) :
    formalRTransform φ (c • a) = PowerSeries.C c * PowerSeries.rescale c (formalRTransform φ a) := by
  ext n
  simp [formalRTransform_coeff, cumulant_replicate_smul, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_rescale, pow_succ, mul_assoc, mul_comm]

end FreeProbability

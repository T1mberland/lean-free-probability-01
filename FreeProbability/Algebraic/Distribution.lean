import FreeProbability.Algebraic.MixedMomentUniqueness
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.Star.Basic

/-!
# Joint distributions of noncommuting variables

Polynomials are the monoid algebra of the free monoid, canonically isomorphic to
mathlib's `FreeAlgebra`. Thus they are finite linear combinations of ordered words,
not commuting polynomials. Star moments use doubled generators `(i, starred)`.
-/

namespace FreeProbability

variable {𝕜 A D I : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
  [Ring D] [Algebra 𝕜 D]

/-- Noncommuting polynomials, in their finite word expansion representation. -/
abbrev WordPolynomial (𝕜 I : Type*) [Semiring 𝕜] := MonoidAlgebra 𝕜 (FreeMonoid I)

/-- Evaluate a noncommuting polynomial at an arbitrary indexed family. -/
noncomputable def evaluate (a : I → A) : WordPolynomial 𝕜 I →ₐ[𝕜] A :=
  MonoidAlgebra.lift 𝕜 A (FreeMonoid I) (FreeMonoid.lift a)

@[simp] theorem evaluate_single (a : I → A) (w : List I) (c : 𝕜) :
    evaluate a (MonoidAlgebra.single (FreeMonoid.ofList w) c) = c • (w.map a).prod := by
  simp [evaluate]

/-- The joint distribution as a linear functional on noncommuting polynomials. -/
noncomputable def jointDistribution (φ : ProbabilitySpace 𝕜 A) (a : I → A) :
    WordPolynomial 𝕜 I →ₗ[𝕜] 𝕜 := φ.expectation.comp (evaluate a).toLinearMap

/-- Ordered joint moment, including the empty word. -/
def jointMoment (φ : ProbabilitySpace 𝕜 A) (a : I → A) (w : List I) : 𝕜 :=
  φ.expectation (w.map a).prod

@[simp] theorem jointMoment_nil (φ : ProbabilitySpace 𝕜 A) (a : I → A) :
    jointMoment φ a [] = 1 := φ.map_one

@[simp] theorem jointDistribution_single (φ : ProbabilitySpace 𝕜 A) (a : I → A)
    (w : List I) (c : 𝕜) :
    jointDistribution φ a (MonoidAlgebra.single (FreeMonoid.ofList w) c) =
      c * jointMoment φ a w := by
  simp [jointDistribution, jointMoment]

/-- Agreement on words implies agreement on every noncommuting polynomial. -/
theorem jointDistribution_eq_iff_moments (φ : ProbabilitySpace 𝕜 A)
    (ψ : ProbabilitySpace 𝕜 D) (a : I → A) (b : I → D) :
    jointDistribution φ a = jointDistribution ψ b ↔
      ∀ w, jointMoment φ a w = jointMoment ψ b w := by
  constructor
  · intro h w
    have := LinearMap.congr_fun h (MonoidAlgebra.single (FreeMonoid.ofList w) 1)
    simpa using this
  · intro h
    apply LinearMap.ext
    intro p
    induction p using MonoidAlgebra.induction_linear with
    | zero => simp
    | add p q hp hq => simp [map_add, hp, hq]
    | single w c =>
      obtain ⟨w, rfl⟩ := FreeMonoid.ofList.surjective w
      simp [h w]

/-- Equality in joint distribution, allowing different ambient algebras. -/
def SameDistribution (φ : ProbabilitySpace 𝕜 A) (ψ : ProbabilitySpace 𝕜 D)
    (a : I → A) (b : I → D) : Prop := ∀ w, jointMoment φ a w = jointMoment ψ b w

/-- Adjoin the starred copy of each generator. -/
def starFamily [Star A] (a : I → A) : I × Bool → A :=
  fun (i, s) => if s then star (a i) else a i

/-- Joint star distribution includes every word in the variables and their adjoints. -/
def SameStarDistribution [Star A] [Star D]
    (φ : ProbabilitySpace 𝕜 A) (ψ : ProbabilitySpace 𝕜 D) (a : I → A) (b : I → D) : Prop :=
  SameDistribution φ ψ (starFamily a) (starFamily b)

namespace FreelyIndependent

/-- Equality of free marginal expectations gives equality of the polynomial joint
distributions of any family chosen from the corresponding subalgebras. -/
theorem jointDistribution_unique {φ ψ : ProbabilitySpace 𝕜 A}
    {B : I → Subalgebra 𝕜 A} (hφ : FreelyIndependent φ B)
    (hψ : FreelyIndependent ψ B)
    (hmarg : ∀ i (x : A), x ∈ B i → φ.expectation x = ψ.expectation x)
    (a : I → A) (ha : ∀ i, a i ∈ B i) :
    jointDistribution φ a = jointDistribution ψ a := by
  apply (jointDistribution_eq_iff_moments _ _ _ _).mpr
  intro w
  have hm : ∀ x ∈ w.map (fun i => (i, a i)), x.2 ∈ B x.1 := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact ha i
  simpa [jointMoment, wordProduct, List.map_map, Function.comp_def] using
    hφ.mixed_moments_unique hψ hmarg (w.map (fun i => (i, a i))) hm

end FreelyIndependent
end FreeProbability

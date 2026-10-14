import FreeProbability.Algebraic.Distribution
import Mathlib.Algebra.Star.UnitaryStarAlgAut

/-! # Expectation-preserving maps and simultaneous unitary conjugation -/

namespace FreeProbability

variable {𝕜 A D I : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
  [Ring D] [Algebra 𝕜 D]

theorem jointMoment_comap (φ : ProbabilitySpace 𝕜 A) (f : D →ₐ[𝕜] A)
    (a : I → D) (w : List I) :
    jointMoment (φ.comap f) a w = jointMoment φ (f ∘ a) w := by
  simp [jointMoment, ProbabilitySpace.comap, map_list_prod, List.map_map, Function.comp_def]

/-- Mapping a family along an expectation-preserving algebra homomorphism keeps
its complete joint distribution. -/
theorem sameDistribution_of_preserving (φ : ProbabilitySpace 𝕜 A)
    (ψ : ProbabilitySpace 𝕜 D) (f : A →ₐ[𝕜] D)
    (hf : ∀ x, ψ.expectation (f x) = φ.expectation x) (a : I → A) :
    SameDistribution φ ψ a (f ∘ a) := by
  intro w
  rw [← jointMoment_comap ψ f a w]
  exact (hf _).symm

namespace IsTracial

variable {φ : ProbabilitySpace 𝕜 A}

/-- Cyclicity of the expectation makes unitary conjugation expectation preserving. -/
theorem expectation_unitary_conjugate [StarMul A] (hφ : IsTracial φ)
    (u : unitary A) (x : A) :
    φ.expectation ((u : A) * x * (star u : A)) = φ.expectation x := by
  rw [hφ ((u : A) * x) (star u : A)]
  simp [← mul_assoc]

/-- Simultaneously conjugating every variable preserves all joint moments. -/
theorem sameDistribution_unitary_conjugate [StarMul A] (hφ : IsTracial φ)
    (u : unitary A) (a : I → A) :
    SameDistribution φ φ a (fun i => (u : A) * a i * (star u : A)) := by
  exact sameDistribution_of_preserving φ φ
    (Unitary.conjStarAlgAut 𝕜 A u).toAlgEquiv.toAlgHom
    (fun x => hφ.expectation_unitary_conjugate u x) a

/-- The same invariance holds for every word in the variables and their adjoints. -/
theorem sameStarDistribution_unitary_conjugate [StarRing A] (hφ : IsTracial φ)
    (u : unitary A) (a : I → A) :
    SameStarDistribution φ φ a (fun i => (u : A) * a i * (star u : A)) := by
  have he : starFamily (fun i => (u : A) * a i * (star u : A)) =
      fun j => (u : A) * starFamily a j * (star u : A) := by
    funext j
    rcases j with ⟨i, s⟩
    cases s <;> simp [starFamily, mul_assoc]
  unfold SameStarDistribution
  rw [he]
  exact hφ.sameDistribution_unitary_conjugate u (starFamily a)

end IsTracial
end FreeProbability

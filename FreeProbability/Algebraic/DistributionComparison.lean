import FreeProbability.Algebraic.Distribution
import Mathlib.Algebra.Algebra.Prod
import Mathlib.RingTheory.Adjoin.Polynomial.Basic

/-!
# Free distributions do not depend on their ambient realization

Compare two families in different algebras by pulling both expectations back
to a paired algebra. Paired polynomial subalgebras encode corresponding marginal
elements. This gives distribution uniqueness without identifying the ambient algebras.
-/

namespace FreeProbability

variable {𝕜 A D I : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
  [Ring D] [Algebra 𝕜 D]

theorem FreelyIndependent.comap {φ : ProbabilitySpace 𝕜 A}
    {B : I → Subalgebra 𝕜 A} (h : FreelyIndependent φ B) (f : D →ₐ[𝕜] A)
    (C : I → Subalgebra 𝕜 D) (hC : ∀ i (x : D), x ∈ C i → f x ∈ B i) :
    FreelyIndependent (φ.comap f) C := by
  intro w hw halt hmem hzero
  let g : I × D → I × A := fun x => (x.1, f x.2)
  have hm : ∀ x ∈ w.map g, x.2 ∈ B x.1 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact hC y.1 y.2 (hmem y hy)
  have hz : ∀ x ∈ w.map g, φ.expectation x.2 = 0 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact hzero y hy
  have hc : (w.map g).IsChain (fun x y => x.1 ≠ y.1) := (List.isChain_map g).mpr halt
  have hp := h (w.map g) (by simpa using hw) hc hm hz
  simpa [g, ProbabilitySpace.comap, map_list_prod, List.map_map, Function.comp_def] using hp

theorem expectation_aeval_eq_of_power_moments (φ : ProbabilitySpace 𝕜 A)
    (ψ : ProbabilitySpace 𝕜 D) (a : A) (b : D)
    (h : ∀ k : ℕ, φ.expectation (a ^ k) = ψ.expectation (b ^ k)) (p : Polynomial 𝕜) :
    φ.expectation (Polynomial.aeval a p) = ψ.expectation (Polynomial.aeval b p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial k c =>
      simp [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one,
        Algebra.smul_mul_assoc, h k]

/-- Free families with the same marginal power moments have the same complete
joint distribution even when realized in different ambient algebras. -/
theorem sameDistribution_of_free_marginals (φ : ProbabilitySpace 𝕜 A)
    (ψ : ProbabilitySpace 𝕜 D) (a : I → A) (b : I → D)
    (hφ : FreelyIndependent φ (fun i => Algebra.adjoin 𝕜 {a i}))
    (hψ : FreelyIndependent ψ (fun i => Algebra.adjoin 𝕜 {b i}))
    (hmarg : ∀ i k, φ.expectation (a i ^ k) = ψ.expectation (b i ^ k)) :
    SameDistribution φ ψ a b := by
  let C : I → Subalgebra 𝕜 (A × D) := fun i => Algebra.adjoin 𝕜 {(a i, b i)}
  let f := AlgHom.fst 𝕜 A D
  let g := AlgHom.snd 𝕜 A D
  have hCf : ∀ i (x : A × D), x ∈ C i → f x ∈ Algebra.adjoin 𝕜 {a i} := by
    intro i x hx
    change x ∈ Algebra.adjoin 𝕜 {(a i, b i)} at hx
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hx
    obtain ⟨p, rfl⟩ := hx
    simp [f, Polynomial.aeval_prod_apply]
  have hCg : ∀ i (x : A × D), x ∈ C i → g x ∈ Algebra.adjoin 𝕜 {b i} := by
    intro i x hx
    change x ∈ Algebra.adjoin 𝕜 {(a i, b i)} at hx
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hx
    obtain ⟨p, rfl⟩ := hx
    simp [g, Polynomial.aeval_prod_apply]
  have hfreeφ := hφ.comap f C hCf
  have hfreeψ := hψ.comap g C hCg
  have hpair : ∀ i (x : A × D), x ∈ C i →
      (φ.comap f).expectation x = (ψ.comap g).expectation x := by
    intro i x hx
    change x ∈ Algebra.adjoin 𝕜 {(a i, b i)} at hx
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hx
    obtain ⟨p, rfl⟩ := hx
    simpa [ProbabilitySpace.comap, f, g, Polynomial.aeval_prod_apply] using
      expectation_aeval_eq_of_power_moments φ ψ (a i) (b i) (hmarg i) p
  intro w
  have hm : ∀ x ∈ w.map (fun i => (i, (a i, b i))), x.2 ∈ C x.1 := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact Algebra.subset_adjoin (Set.mem_singleton _)
  have he := hfreeφ.mixed_moments_unique hfreeψ hpair _ hm
  simpa [jointMoment, ProbabilitySpace.comap, wordProduct, f, g,
    List.map_map, Function.comp_def, map_list_prod] using he

/-- For self-adjoint free families, marginal power moments also determine their
complete joint star distribution across different ambient realizations. -/
theorem sameStarDistribution_of_selfAdjoint_free_marginals [StarRing A] [StarRing D]
    (φ : ProbabilitySpace 𝕜 A) (ψ : ProbabilitySpace 𝕜 D) (a : I → A) (b : I → D)
    (ha : ∀ i, star (a i) = a i) (hb : ∀ i, star (b i) = b i)
    (hφ : FreelyIndependent φ (fun i => Algebra.adjoin 𝕜 {a i}))
    (hψ : FreelyIndependent ψ (fun i => Algebra.adjoin 𝕜 {b i}))
    (hmarg : ∀ i k, φ.expectation (a i ^ k) = ψ.expectation (b i ^ k)) :
    SameStarDistribution φ ψ a b := by
  have h := sameDistribution_of_free_marginals φ ψ a b hφ hψ hmarg
  intro w
  have hea : starFamily a = a ∘ Prod.fst := by funext j; simp [starFamily, ha]
  have heb : starFamily b = b ∘ Prod.fst := by funext j; simp [starFamily, hb]
  simpa [jointMoment, hea, heb, List.map_map, Function.comp_def] using h (w.map Prod.fst)

end FreeProbability

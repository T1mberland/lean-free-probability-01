import FreeProbability.Algebraic.ProbabilitySpace
import Mathlib.Data.List.Chain
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

/-!
# Scalar-valued free independence

Words carry a subalgebra label for each letter. Alternation means adjacent labels
differ; repeated nonadjacent labels are allowed. The empty word is excluded from
the vanishing condition because its expectation is one.
-/

namespace FreeProbability

variable {𝕜 A I : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]

/-- Voiculescu's centered alternating-word definition for unital subalgebras. -/
def FreelyIndependent (φ : ProbabilitySpace 𝕜 A) (B : I → Subalgebra 𝕜 A) : Prop :=
  ∀ (w : List (I × A)), w ≠ [] →
    w.IsChain (fun x y => x.1 ≠ y.1) →
    (∀ x ∈ w, x.2 ∈ B x.1) →
    (∀ x ∈ w, φ.expectation x.2 = 0) →
    φ.expectation (w.map Prod.snd).prod = 0

namespace FreelyIndependent

variable {φ : ProbabilitySpace 𝕜 A} {B : I → Subalgebra 𝕜 A}

/-- Passing to smaller unital subalgebras preserves free independence. -/
theorem mono (h : FreelyIndependent φ B) {C : I → Subalgebra 𝕜 A}
    (hCB : ∀ i, C i ≤ B i) : FreelyIndependent φ C := by
  intro w hw halt hmem hzero
  exact h w hw halt (fun x hx => hCB x.1 (hmem x hx)) hzero

/-- An injective relabeling selects a free subfamily. -/
theorem reindex {J : Type*} (h : FreelyIndependent φ B) (f : J → I)
    (hf : Function.Injective f) : FreelyIndependent φ (B ∘ f) := by
  intro w hw halt hmem hzero
  let g : J × A → I × A := fun x => (f x.1, x.2)
  have halt' : (w.map g).IsChain (fun x y => x.1 ≠ y.1) :=
    (List.isChain_map g).mpr (halt.imp (fun x y hxy h => hxy (hf h)))
  have hm : ∀ x ∈ w.map g, x.2 ∈ B x.1 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact hmem y hy
  have hz : ∀ x ∈ w.map g, φ.expectation x.2 = 0 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact hzero y hy
  simpa [g, List.map_map, Function.comp_def] using
    h (w.map g) (by simpa using hw) halt' hm hz

theorem centered_pair (h : FreelyIndependent φ B) {i j : I} (hij : i ≠ j)
    {a b : A} (ha : a ∈ B i) (hb : b ∈ B j) :
    φ.expectation (φ.center a * φ.center b) = 0 := by
  simpa using h [(i, φ.center a), (j, φ.center b)] (by simp)
    (by simpa using hij)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false];
        rintro x (rfl | rfl)
        · exact φ.center_mem _ ha
        · exact φ.center_mem _ hb)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false];
        rintro x (rfl | rfl) <;> exact φ.expectation_center _)

/-- The mixed second moment of free subalgebras factors. -/
theorem expectation_mul (h : FreelyIndependent φ B) {i j : I} (hij : i ≠ j)
    {a b : A} (ha : a ∈ B i) (hb : b ∈ B j) :
    φ.expectation (a * b) = φ.expectation a * φ.expectation b := by
  have hc := h.centered_pair hij ha hb
  have he : φ.expectation (φ.center a * φ.center b) =
      φ.expectation (a * b) - φ.expectation a * φ.expectation b := by
    simp only [ProbabilitySpace.center, sub_mul, mul_sub, map_sub,
      Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
      Algebra.algebraMap_eq_smul_one, one_mul, mul_one, map_smul,
      ProbabilitySpace.expectation_one, smul_eq_mul]
    ring
  rw [he] at hc
  exact sub_eq_zero.mp hc

end FreelyIndependent
end FreeProbability

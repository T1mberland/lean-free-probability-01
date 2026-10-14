import FreeProbability.Algebraic.Freeness

/-!
# Algebraic conditional expectations and freeness with amalgamation

The base algebra is an actual unital subalgebra. The expectation is a linear
retraction and a bimodule map. Positivity and normality are analytic extensions.
Amalgamated freeness does not in general imply scalar freeness.
-/

namespace FreeProbability

variable {𝕜 A I : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]

/-- Algebraic conditional expectation onto a fixed unital subalgebra. -/
structure ConditionalExpectation (B : Subalgebra 𝕜 A) where
  toLinearMap : A →ₗ[𝕜] B
  fixes : ∀ b : B, toLinearMap (b : A) = b
  map_mul_left : ∀ (b : B) (a : A), toLinearMap ((b : A) * a) = b * toLinearMap a
  map_mul_right : ∀ (a : A) (b : B), toLinearMap (a * (b : A)) = toLinearMap a * b

namespace ConditionalExpectation

variable {B : Subalgebra 𝕜 A} (E : ConditionalExpectation B)

@[simp] theorem map_one : E.toLinearMap 1 = 1 := E.fixes 1

@[simp] theorem idempotent (a : A) : E.toLinearMap (E.toLinearMap a : A) = E.toLinearMap a :=
  E.fixes _

theorem bimodule (b c : B) (a : A) :
    E.toLinearMap ((b : A) * a * (c : A)) = b * E.toLinearMap a * c := by
  rw [E.map_mul_right, E.map_mul_left]

/-- The part in the kernel of the conditional expectation. -/
def center (a : A) : A := a - (E.toLinearMap a : A)

@[simp] theorem map_center (a : A) : E.toLinearMap (E.center a) = 0 := by
  simp [center, map_sub, E.idempotent]

@[simp] theorem center_base (b : B) : E.center (b : A) = 0 := by
  simp [center, E.fixes]

theorem center_mem {C : Subalgebra 𝕜 A} (hBC : B ≤ C) {a : A} (ha : a ∈ C) :
    E.center a ∈ C := C.sub_mem ha (hBC (E.toLinearMap a).property)

theorem decomposition (a : A) : E.center a + (E.toLinearMap a : A) = a := by
  simp [center]

/-- The centered/base decomposition is unique. -/
theorem decomposition_unique (a c : A) (b : B)
    (hc : E.toLinearMap c = 0) (h : c + (b : A) = a) :
    c = E.center a ∧ b = E.toLinearMap a := by
  have hb : b = E.toLinearMap a := by
    rw [← h, map_add, hc, E.fixes, zero_add]
  constructor
  · rw [center, ← hb, ← h]
    abel
  · exact hb

/-- Compose a scalar normalized expectation on the base with the conditional expectation. -/
def toProbabilitySpace (φ : ProbabilitySpace 𝕜 B) : ProbabilitySpace 𝕜 A where
  expectation := φ.expectation.comp E.toLinearMap
  map_one := by simp [E.map_one]

@[simp] theorem toProbabilitySpace_base (φ : ProbabilitySpace 𝕜 B) (b : B) :
    (E.toProbabilitySpace φ).expectation (b : A) = φ.expectation b := by
  simp [toProbabilitySpace, E.fixes]

end ConditionalExpectation

/-- Freeness with amalgamation over `B`, including the required common base inclusion. -/
def FreelyIndependentOver {B : Subalgebra 𝕜 A} (E : ConditionalExpectation B)
    (C : I → Subalgebra 𝕜 A) : Prop :=
  (∀ i, B ≤ C i) ∧
  ∀ w : List (I × A), w ≠ [] → w.IsChain (fun x y => x.1 ≠ y.1) →
    (∀ x ∈ w, x.2 ∈ C x.1) → (∀ x ∈ w, E.toLinearMap x.2 = 0) →
    E.toLinearMap (w.map Prod.snd).prod = 0

namespace FreelyIndependentOver

variable {B : Subalgebra 𝕜 A} {E : ConditionalExpectation B} {C : I → Subalgebra 𝕜 A}

theorem centered_pair (h : FreelyIndependentOver E C) {i j : I} (hij : i ≠ j)
    {a b : A} (ha : a ∈ C i) (hb : b ∈ C j) :
    E.toLinearMap (E.center a * E.center b) = 0 := by
  simpa using h.2 [(i, E.center a), (j, E.center b)] (by simp) (by simpa using hij)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false];
        rintro x (rfl | rfl)
        · exact E.center_mem (h.1 i) ha
        · exact E.center_mem (h.1 j) hb)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false];
        rintro x (rfl | rfl) <;> exact E.map_center _)

/-- The operator-valued mixed second moment factors in the base algebra,
preserving the order of its noncommuting factors. -/
theorem expectation_mul (h : FreelyIndependentOver E C) {i j : I} (hij : i ≠ j)
    {a b : A} (ha : a ∈ C i) (hb : b ∈ C j) :
    E.toLinearMap (a * b) = E.toLinearMap a * E.toLinearMap b := by
  have hz := h.centered_pair hij ha hb
  simp only [ConditionalExpectation.center, sub_mul, mul_sub, map_sub,
    E.map_mul_left, E.map_mul_right, E.idempotent] at hz
  simp only [sub_self, sub_zero] at hz
  exact sub_eq_zero.mp hz

end FreelyIndependentOver
end FreeProbability

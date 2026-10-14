import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.BigOperators.Group.List.Defs

/-!
# Algebraic noncommutative probability spaces

This layer requires a unital linear functional, without assuming positivity or a trace.
Analytic and tracial spaces extend this interface rather than changing its meaning.
-/

namespace FreeProbability

variable (𝕜 A : Type*) [Field 𝕜] [Ring A] [Algebra 𝕜 A]

/-- An algebraic noncommutative probability space on a fixed algebra. -/
structure ProbabilitySpace where
  expectation : A →ₗ[𝕜] 𝕜
  map_one : expectation 1 = 1

variable {𝕜 A}

namespace ProbabilitySpace

variable (φ : ProbabilitySpace 𝕜 A)

@[simp] theorem expectation_one : φ.expectation 1 = 1 := φ.map_one

include φ in
/-- A normalized functional into a field excludes the trivial ambient algebra. -/
theorem nontrivial : Nontrivial A := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  have hf := congrArg φ.expectation h
  simp only [map_zero, φ.map_one] at hf
  exact zero_ne_one hf

@[simp] theorem expectation_algebraMap (c : 𝕜) :
    φ.expectation (algebraMap 𝕜 A c) = c := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, φ.map_one, smul_eq_mul, mul_one]

/-- Subtract the scalar expectation, viewed as a central algebra element. -/
def center (a : A) : A := a - algebraMap 𝕜 A (φ.expectation a)

@[simp] theorem expectation_center (a : A) : φ.expectation (φ.center a) = 0 := by
  simp [center]

@[simp] theorem center_of_expectation_eq_zero {a : A} (h : φ.expectation a = 0) :
    φ.center a = a := by simp [center, h]

theorem center_mem (B : Subalgebra 𝕜 A) {a : A} (ha : a ∈ B) : φ.center a ∈ B :=
  B.sub_mem ha (B.algebraMap_mem _)

theorem center_add_expectation (a : A) :
    φ.center a + algebraMap 𝕜 A (φ.expectation a) = a := by
  simp [center]

@[simp] theorem center_center (a : A) : φ.center (φ.center a) = φ.center a := by simp

@[simp] theorem center_algebraMap (c : 𝕜) : φ.center (algebraMap 𝕜 A c) = 0 := by
  simp [center]

/-- Restriction to a unital subalgebra. -/
def restrict (B : Subalgebra 𝕜 A) : ProbabilitySpace 𝕜 B where
  expectation := φ.expectation.comp B.val.toLinearMap
  map_one := by simp

@[simp] theorem restrict_expectation (B : Subalgebra 𝕜 A) (a : B) :
    (φ.restrict B).expectation a = φ.expectation (a : A) := rfl

/-- Pull back along a unital algebra homomorphism. -/
def comap {D : Type*} [Ring D] [Algebra 𝕜 D] (f : D →ₐ[𝕜] A) :
    ProbabilitySpace 𝕜 D where
  expectation := φ.expectation.comp f.toLinearMap
  map_one := by simp

end ProbabilitySpace

/-- Traciality is a separate property of the expectation. -/
def IsTracial (φ : ProbabilitySpace 𝕜 A) : Prop :=
  ∀ a b : A, φ.expectation (a * b) = φ.expectation (b * a)

end FreeProbability

import FreeProbability.Algebraic.Distribution
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.Algebra.Bilinear

/-!
# Algebraic free difference quotients

The codomain is the genuine algebraic tensor bimodule of noncommutative
polynomials. Left multiplication acts on the first factor, and right
multiplication on the second. No tensor completion is needed for polynomials.
-/

noncomputable section
open scoped TensorProduct Classical
namespace FreeProbability

variable {𝕜 I : Type*} [Field 𝕜]

abbrev PolynomialTensor (𝕜 I : Type*) [Field 𝕜] :=
  WordPolynomial 𝕜 I ⊗[𝕜] WordPolynomial 𝕜 I

def wordMonomial (w : List I) : WordPolynomial 𝕜 I :=
  MonoidAlgebra.single (FreeMonoid.ofList w) 1

@[simp] theorem wordMonomial_nil : wordMonomial ([] : List I) = (1 : WordPolynomial 𝕜 I) := by
  simp [wordMonomial, MonoidAlgebra.one_def]

@[simp] theorem wordMonomial_append (u v : List I) :
    wordMonomial (𝕜 := 𝕜) (u ++ v) = wordMonomial u * wordMonomial v := by
  simp [wordMonomial, MonoidAlgebra.single_mul_single]

def tensorLeft (p : WordPolynomial 𝕜 I) : PolynomialTensor 𝕜 I →ₗ[𝕜] PolynomialTensor 𝕜 I :=
  (LinearMap.mul 𝕜 (WordPolynomial 𝕜 I) p).rTensor (WordPolynomial 𝕜 I)

def tensorRight (q : WordPolynomial 𝕜 I) : PolynomialTensor 𝕜 I →ₗ[𝕜] PolynomialTensor 𝕜 I :=
  ((LinearMap.mul 𝕜 (WordPolynomial 𝕜 I)).flip q).lTensor (WordPolynomial 𝕜 I)

@[simp] theorem tensorLeft_tmul (p a b : WordPolynomial 𝕜 I) :
    tensorLeft p (a ⊗ₜ[𝕜] b) = (p * a) ⊗ₜ[𝕜] b := by simp [tensorLeft]

@[simp] theorem tensorRight_tmul (q a b : WordPolynomial 𝕜 I) :
    tensorRight q (a ⊗ₜ[𝕜] b) = a ⊗ₜ[𝕜] (b * q) := by simp [tensorRight]

@[simp] theorem tensorLeft_one (z : PolynomialTensor 𝕜 I) : tensorLeft 1 z = z := by
  induction z using TensorProduct.inductionOn with
  | tmul a b => simp
  | add x y hx hy => simp [hx, hy]

@[simp] theorem tensorRight_one (z : PolynomialTensor 𝕜 I) : tensorRight 1 z = z := by
  induction z using TensorProduct.inductionOn with
  | tmul a b => simp
  | add x y hx hy => simp [hx, hy]

theorem tensorLeft_mul (p q : WordPolynomial 𝕜 I) (z : PolynomialTensor 𝕜 I) :
    tensorLeft (p * q) z = tensorLeft p (tensorLeft q z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b => simp [mul_assoc]
  | add x y hx hy => simp [hx, hy]

theorem tensorLeft_right (p q : WordPolynomial 𝕜 I) (z : PolynomialTensor 𝕜 I) :
    tensorLeft p (tensorRight q z) = tensorRight q (tensorLeft p z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b => simp
  | add x y hx hy => simp [hx, hy]

/-- The recursive derivative of an ordered word. -/
def wordDifferenceQuotient (i : I) : List I → PolynomialTensor 𝕜 I
  | [] => 0
  | j :: w => (if i = j then (1 : WordPolynomial 𝕜 I) ⊗ₜ[𝕜] wordMonomial w else 0) +
      tensorLeft (wordMonomial [j]) (wordDifferenceQuotient i w)

@[simp] theorem wordDifferenceQuotient_nil (i : I) :
    wordDifferenceQuotient (𝕜 := 𝕜) i [] = 0 := rfl

/-- Linear extension to the existing noncommutative polynomial interface. -/
def freeDifferenceQuotient (i : I) : WordPolynomial 𝕜 I →ₗ[𝕜] PolynomialTensor 𝕜 I :=
  (Finsupp.linearCombination 𝕜 (fun w : FreeMonoid I => wordDifferenceQuotient i w.toList)).comp
    (MonoidAlgebra.coeffLinearEquiv 𝕜).toLinearMap

@[simp] theorem freeDifferenceQuotient_single (i : I) (w : List I) (c : 𝕜) :
    freeDifferenceQuotient i (MonoidAlgebra.single (FreeMonoid.ofList w) c) =
      c • wordDifferenceQuotient (𝕜 := 𝕜) i w := by
  simp only [freeDifferenceQuotient, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, MonoidAlgebra.coeffLinearEquiv_apply,
    MonoidAlgebra.coeff_single, Finsupp.linearCombination_single, FreeMonoid.toList_ofList]

@[simp] theorem freeDifferenceQuotient_generator (i j : I) :
    freeDifferenceQuotient i (wordMonomial (𝕜 := 𝕜) [j]) =
      if i = j then (1 : WordPolynomial 𝕜 I) ⊗ₜ[𝕜] (1 : WordPolynomial 𝕜 I) else 0 := by
  change freeDifferenceQuotient i (MonoidAlgebra.single (FreeMonoid.ofList [j]) 1) = _
  rw [freeDifferenceQuotient_single]
  simp [wordDifferenceQuotient]

/-- The ordered word derivative satisfies the noncommutative tensor Leibniz rule. -/
theorem wordDifferenceQuotient_append (i : I) (u v : List I) :
    wordDifferenceQuotient (𝕜 := 𝕜) i (u ++ v) =
      tensorLeft (wordMonomial u) (wordDifferenceQuotient i v) +
        tensorRight (wordMonomial v) (wordDifferenceQuotient i u) := by
  induction u with
  | nil => simp [wordDifferenceQuotient]
  | cons j u ih =>
    simp only [List.cons_append, wordDifferenceQuotient, ih, map_add]
    have hm : wordMonomial (𝕜 := 𝕜) (j :: u) = wordMonomial [j] * wordMonomial u :=
      wordMonomial_append [j] u
    rw [hm, tensorLeft_mul, tensorLeft_right]
    by_cases h : i = j <;> simp [h, wordMonomial_append, add_left_comm]

end FreeProbability

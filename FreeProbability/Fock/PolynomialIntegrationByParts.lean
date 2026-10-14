import FreeProbability.Algebraic.FreeDifferenceQuotient
import FreeProbability.Fock.WordIntegrationByParts

/-!
# Free integration by parts for all noncommutative polynomials

The actual Fock vacuum expectation contracts the actual algebraic tensor-valued
free difference quotient. Neither a Wick formula nor an IBP assumption is used.
-/

noncomputable section
open scoped TensorProduct Classical
namespace FreeProbability

variable {𝕜 A I : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]

/-- The tensor product expectation after polynomial evaluation. -/
def tensorPolynomialExpectation (φ : ProbabilitySpace 𝕜 A) (a : I → A) :
    PolynomialTensor 𝕜 I →ₗ[𝕜] 𝕜 :=
  TensorProduct.lift ((LinearMap.mul 𝕜 𝕜).compl₁₂
    (jointDistribution φ a) (jointDistribution φ a))

@[simp] theorem tensorPolynomialExpectation_tmul (φ : ProbabilitySpace 𝕜 A)
    (a : I → A) (p q : WordPolynomial 𝕜 I) :
    tensorPolynomialExpectation φ a (p ⊗ₜ[𝕜] q) =
      φ.expectation (evaluate a p) * φ.expectation (evaluate a q) := rfl

namespace Fock

/-- Free integration by parts for every polynomial in the actual semicircular operators. -/
theorem vacuumState_polynomial_integrationByParts (i : I) (p : WordPolynomial ℂ I) :
    (vacuumState I).expectation (semicircular i * evaluate semicircular p) =
      tensorPolynomialExpectation (vacuumState I).toProbabilitySpace semicircular
        (freeDifferenceQuotient i p) := by
  induction p using MonoidAlgebra.induction_linear with
  | zero => simp [vacuumExpectation]
  | add p q hp hq => simp [map_add, mul_add, hp, hq]
  | single w c =>
    obtain ⟨w, rfl⟩ := FreeMonoid.ofList.surjective w
    rw [evaluate_single, freeDifferenceQuotient_single]
    simp only [mul_smul_comm, map_smul]
    congr 1
    change vacuumExpectation (operatorWord (i :: w)) = _
    rw [vacuumExpectation_operatorWord_cons, wordDifferenceQuotient_eq_sum, map_sum]
    apply Finset.sum_congr rfl
    intro k _
    by_cases h : i = w.get k
    · simp only [List.get_eq_getElem] at h
      simp [h, tensorPolynomialExpectation_tmul, wordMonomial, evaluate_single, operatorWord]
    · simp only [List.get_eq_getElem] at h
      simp [h]

end Fock
end FreeProbability

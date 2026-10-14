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

/-- Evaluation in the closed generated algebra agrees with the concrete operators. -/
theorem coe_evaluate_closedSemicircular (p : WordPolynomial ℂ I) :
    (closedSemicircularAlgebra I).val (evaluate closedSemicircular p) =
      evaluate semicircular p := by
  induction p using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq =>
    simp only [map_add]
    exact congrArg₂ (· + ·) hp hq
  | single w c =>
    obtain ⟨w, rfl⟩ := FreeMonoid.ofList.surjective w
    simp only [evaluate_single, map_smul, map_list_prod, List.map_map]
    rfl

/-- Tensor expectations agree under the actual inclusion of the closed C-star model. -/
theorem tensorPolynomialExpectation_closedGeneratedVacuumState :
    tensorPolynomialExpectation (closedGeneratedVacuumState I).toProbabilitySpace
      closedSemicircular = tensorPolynomialExpectation (vacuumState I).toProbabilitySpace
      semicircular := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul p q =>
    simp only [tensorPolynomialExpectation_tmul]
    change vacuumExpectation ((closedSemicircularAlgebra I).val (evaluate closedSemicircular p)) *
      vacuumExpectation ((closedSemicircularAlgebra I).val (evaluate closedSemicircular q)) = _
    rw [coe_evaluate_closedSemicircular, coe_evaluate_closedSemicircular]
    rfl
  | add x y hx hy => simp [map_add, hx, hy]

/-- Polynomial integration by parts in the actual faithful tracial C-star probability space. -/
theorem closedGeneratedVacuumState_polynomial_integrationByParts (i : I)
    (p : WordPolynomial ℂ I) :
    (closedGeneratedVacuumState I).expectation
      (closedSemicircular i * evaluate closedSemicircular p) =
      tensorPolynomialExpectation (closedGeneratedVacuumState I).toProbabilitySpace
        closedSemicircular (freeDifferenceQuotient i p) := by
  rw [tensorPolynomialExpectation_closedGeneratedVacuumState]
  change vacuumExpectation ((closedSemicircularAlgebra I).val
    (closedSemicircular i * evaluate closedSemicircular p)) = _
  rw [map_mul, coe_evaluate_closedSemicircular]
  exact vacuumState_polynomial_integrationByParts i p

end Fock
end FreeProbability

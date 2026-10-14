import FreeProbability.Analytic.FockExponentialPolynomial
import FreeProbability.Fock.CStarModel

/-! # Entire polynomial exponential IBP in the actual faithful tracial closed C-star model -/

noncomputable section
open scoped Classical TensorProduct
open NormedSpace

namespace FreeProbability.Fock

variable {I : Type*}

local instance : NormedAlgebra ℚ (closedSemicircularAlgebra I) :=
  .restrictScalars ℚ ℂ _

/-- The exponential in the closed C-star algebra is the actual bounded-operator exponential. -/
theorem coe_exp_closedSemicircularAlgebra (X : closedSemicircularAlgebra I) :
    (closedSemicircularAlgebra I).val (exp X : closedSemicircularAlgebra I) =
      exp ((closedSemicircularAlgebra I).val X) :=
  map_exp (show closedSemicircularAlgebra I →ₐ[ℂ] (WordSpace I →L[ℂ] WordSpace I) from
    (closedSemicircularAlgebra I).val) continuous_subtype_val X

/-- The actual inclusion preserves real scalar multiplication as well as complex scalars. -/
theorem coe_real_smul_closedSemicircularAlgebra (r : ℝ) (X : closedSemicircularAlgebra I) :
    (closedSemicircularAlgebra I).val (r • X) = r • (closedSemicircularAlgebra I).val X := rfl

/-- Ordered tensor contraction using the actual faithful tracial C-star state itself. -/
def closedSandwichPolynomialExpectation (L R : closedSemicircularAlgebra I) :
    PolynomialTensor ℂ I →ₗ[ℂ] ℂ :=
  TensorProduct.lift ((LinearMap.mul ℂ ℂ).compl₁₂
    ((closedGeneratedVacuumState I).expectation.comp
      ((LinearMap.mul ℂ _ L).comp (evaluate closedSemicircular).toLinearMap))
    ((closedGeneratedVacuumState I).expectation.comp
      (((LinearMap.mul ℂ _).flip R).comp (evaluate closedSemicircular).toLinearMap)))

@[simp] theorem closedSandwichPolynomialExpectation_tmul (L R : closedSemicircularAlgebra I)
    (p q : WordPolynomial ℂ I) :
    closedSandwichPolynomialExpectation L R (p ⊗ₜ[ℂ] q) =
      (closedGeneratedVacuumState I).expectation (L * evaluate closedSemicircular p) *
        (closedGeneratedVacuumState I).expectation (evaluate closedSemicircular q * R) := rfl

/-- The closed-state tensor contraction is precisely its concrete operator vacuum contraction. -/
theorem closedSandwichPolynomialExpectation_eq (L R : closedSemicircularAlgebra I) :
    closedSandwichPolynomialExpectation L R =
      sandwichPolynomialExpectation ((closedSemicircularAlgebra I).val L)
        ((closedSemicircularAlgebra I).val R) := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul p q =>
    simp only [closedSandwichPolynomialExpectation_tmul, sandwichPolynomialExpectation_tmul]
    change vacuumExpectation ((closedSemicircularAlgebra I).val (L * evaluate closedSemicircular p)) *
      vacuumExpectation ((closedSemicircularAlgebra I).val (evaluate closedSemicircular q * R)) = _
    rw [map_mul, map_mul, coe_evaluate_closedSemicircular, coe_evaluate_closedSemicircular]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Exact all-polynomial, entire complex-parameter exponential IBP inside the actual
faithful tracial closed C-star probability space, with its own tensor contraction. -/
theorem closedGeneratedVacuumState_polynomial_exp_integrationByParts
    (i : I) (p : WordPolynomial ℂ I) (t : ℂ) :
    (closedGeneratedVacuumState I).expectation
      (closedSemicircular i * exp (t • evaluate closedSemicircular p)) =
      t * (∫ u in (0 : ℝ)..1, closedSandwichPolynomialExpectation
        (exp ((1 - u) • (t • evaluate closedSemicircular p)))
        (exp (u • (t • evaluate closedSemicircular p))) (freeDifferenceQuotient i p)) := by
  change vacuumExpectation ((closedSemicircularAlgebra I).val
    (closedSemicircular i * exp (t • evaluate closedSemicircular p))) = _
  rw [map_mul, coe_exp_closedSemicircularAlgebra, map_smul, coe_evaluate_closedSemicircular]
  simp_rw [closedSandwichPolynomialExpectation_eq]
  simp_rw [coe_exp_closedSemicircularAlgebra, coe_real_smul_closedSemicircularAlgebra,
    map_smul, coe_evaluate_closedSemicircular]
  exact vacuumExpectation_scaled_polynomial_exp_integrationByParts i p t

end FreeProbability.Fock

import FreeProbability.Analytic.FockExponentialIntegrationByParts
import FreeProbability.Fock.PolynomialIntegrationByParts

/-!
# Exponential IBP for arbitrary noncommutative polynomials

The derivative is the existing algebraic tensor-valued free difference quotient.
Its evaluation inserts the actual rank-one vacuum projection, and the Duhamel
integral contracts its two factors against ordered exponential vacuum states.
-/

noncomputable section
open scoped Classical TensorProduct
open NormedSpace

namespace FreeProbability.Fock

variable {I : Type*}

/-- The actual operator commutator, as a linear map. -/
def operatorCommutator (C : WordSpace I →L[ℂ] WordSpace I) :
    (WordSpace I →L[ℂ] WordSpace I) →ₗ[ℂ] (WordSpace I →L[ℂ] WordSpace I) :=
  LinearMap.mul ℂ _ C - (LinearMap.mul ℂ _).flip C

@[simp] theorem operatorCommutator_apply (C X : WordSpace I →L[ℂ] WordSpace I) :
    operatorCommutator C X = C * X - X * C := rfl

/-- Evaluation of the polynomial tensor derivative by actual vacuum rank-one insertion. -/
def polynomialRankOneInsertion : PolynomialTensor ℂ I →ₗ[ℂ] (WordSpace I →L[ℂ] WordSpace I) :=
  TensorProduct.lift ((LinearMap.mul ℂ (WordSpace I →L[ℂ] WordSpace I)).compl₁₂
    (((LinearMap.mul ℂ (WordSpace I →L[ℂ] WordSpace I)).flip vacuumProjection).comp
      (evaluate semicircular).toLinearMap)
    (evaluate semicircular).toLinearMap)

@[simp] theorem polynomialRankOneInsertion_tmul (p q : WordPolynomial ℂ I) :
    polynomialRankOneInsertion (p ⊗ₜ[ℂ] q) =
      evaluate semicircular p * vacuumProjection * evaluate semicircular q := rfl

/-- The existing polynomial FDQ is exactly the actual right-annihilation boundary commutator. -/
theorem rightAnnihilation_polynomial_commutator (i : I) (p : WordPolynomial ℂ I) :
    operatorCommutator (rightAnnihilation i) (evaluate semicircular p) =
      polynomialRankOneInsertion (freeDifferenceQuotient i p) := by
  induction p using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single w c =>
    obtain ⟨w, rfl⟩ := FreeMonoid.ofList.surjective w
    rw [evaluate_single, freeDifferenceQuotient_single]
    simp only [map_smul]
    congr 1
    change rightAnnihilation i * (w.map semicircular).prod -
      (w.map semicircular).prod * rightAnnihilation i = _
    rw [commutator_list_prod, wordDifferenceQuotient_eq_sum, map_sum]
    apply Fintype.sum_equiv (finCongr (List.length_map (as := w) semicircular))
    intro k
    have hk : (finCongr (List.length_map (as := w) semicircular) k).val = k.val := rfl
    simp only [hk, ← List.map_take, ← List.map_drop, List.get_eq_getElem, List.getElem_map]
    rw [rightAnnihilation_semicircular_commutator]
    by_cases h : i = w[k.val]
    · simp [h, polynomialRankOneInsertion_tmul, wordMonomial, evaluate_single]
    · simp [h]

/-- The polynomial tensor derivative contracted against ordered left/right vacuum factors. -/
def sandwichPolynomialExpectation (L R : WordSpace I →L[ℂ] WordSpace I) :
    PolynomialTensor ℂ I →ₗ[ℂ] ℂ :=
  TensorProduct.lift ((LinearMap.mul ℂ ℂ).compl₁₂
    (vacuumLinear.comp ((LinearMap.mul ℂ _ L).comp (evaluate semicircular).toLinearMap))
    (vacuumLinear.comp (((LinearMap.mul ℂ _).flip R).comp (evaluate semicircular).toLinearMap)))

@[simp] theorem sandwichPolynomialExpectation_tmul (L R : WordSpace I →L[ℂ] WordSpace I)
    (p q : WordPolynomial ℂ I) :
    sandwichPolynomialExpectation L R (p ⊗ₜ[ℂ] q) =
      vacuumExpectation (L * evaluate semicircular p) *
        vacuumExpectation (evaluate semicircular q * R) := rfl

/-- Actual rank-one insertion splits the ordered tensor contraction, for every polynomial tensor. -/
theorem vacuumExpectation_sandwichRankOne (L R : WordSpace I →L[ℂ] WordSpace I)
    (z : PolynomialTensor ℂ I) :
    vacuumExpectation (L * polynomialRankOneInsertion z * R) =
      sandwichPolynomialExpectation L R z := by
  induction z using TensorProduct.inductionOn with
  | tmul p q =>
    rw [polynomialRankOneInsertion_tmul, sandwichPolynomialExpectation_tmul]
    rw [show L * (evaluate semicircular p * vacuumProjection * evaluate semicircular q) * R =
      (L * evaluate semicircular p) * vacuumProjection * (evaluate semicircular q * R) by
        noncomm_ring]
    exact vacuumExpectation_mul_vacuumProjection_mul _ _
  | add x y hx hy =>
    change vacuumLinear (L * polynomialRankOneInsertion (x + y) * R) = _
    simp only [map_add, mul_add, add_mul]
    exact congrArg₂ (· + ·) hx hy

/-- Exact entire exponential IBP for every noncommutative polynomial.
The FDQ is evaluated in its actual algebraic tensor bimodule, with exponential sandwich factors. -/
theorem vacuumExpectation_polynomial_exp_integrationByParts (i : I) (p : WordPolynomial ℂ I) :
    vacuumExpectation (semicircular i * exp (evaluate semicircular p)) =
      ∫ u in (0 : ℝ)..1, sandwichPolynomialExpectation
        (exp ((1 - u) • evaluate semicircular p)) (exp (u • evaluate semicircular p))
        (freeDifferenceQuotient i p) := by
  rw [vacuumExpectation_semicircular_mul_exp]
  have h := rightAnnihilation_polynomial_commutator i p
  simp only [operatorCommutator_apply] at h
  simp_rw [h, vacuumExpectation_sandwichRankOne]

/-- The complex exponential parameter is unrestricted for every polynomial. -/
theorem vacuumExpectation_scaled_polynomial_exp_integrationByParts
    (i : I) (p : WordPolynomial ℂ I) (t : ℂ) :
    vacuumExpectation (semicircular i * exp (t • evaluate semicircular p)) =
      t * (∫ u in (0 : ℝ)..1, sandwichPolynomialExpectation
        (exp ((1 - u) • (t • evaluate semicircular p)))
        (exp (u • (t • evaluate semicircular p))) (freeDifferenceQuotient i p)) := by
  have h := vacuumExpectation_polynomial_exp_integrationByParts i (t • p)
  simp only [map_smul, smul_eq_mul] at h
  rw [h]
  exact intervalIntegral.integral_const_mul t _

end FreeProbability.Fock

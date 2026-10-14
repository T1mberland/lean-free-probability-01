import FreeProbability.Analytic.FockExponentialDuhamel
import FreeProbability.Fock.WordIntegrationByParts

/-!
# Entire exponential integration by parts for actual Fock operators

The Duhamel commutator and the genuine vacuum boundary identity give exact
integral identities for bounded-operator exponentials. The complex scalar
parameter is unrestricted; no formal power-series identity substitutes for the
actual exponential.
-/

noncomputable section
open scoped Classical
open NormedSpace

namespace FreeProbability.Fock

variable {I : Type*}

/-- Actual exponential IBP for every bounded operator, with its ordered boundary commutator. -/
theorem vacuumExpectation_semicircular_mul_exp (i : I)
    (X : WordSpace I →L[ℂ] WordSpace I) :
    vacuumExpectation (semicircular i * exp X) =
      ∫ u in (0 : ℝ)..1, vacuumExpectation
        (exp ((1 - u) • X) * (rightAnnihilation i * X - X * rightAnnihilation i) *
          exp (u • X)) := by
  rw [← vacuumExpectation_rightAnnihilation_commutator, exponential_commutator_eq_integral]
  exact ((vacuumContinuous I).intervalIntegral_comp_comm
    ((continuous_exponentialCommutatorIntegrand (rightAnnihilation i) X).intervalIntegrable 0 1)).symm

/-- The exact boundary commutator with a complex scalar multiple of a canonical field. -/
theorem rightAnnihilation_scaled_semicircular_commutator (i j : I) (t : ℂ) :
    rightAnnihilation i * (t • semicircular j) - (t • semicircular j) * rightAnnihilation i =
      if i = j then t • vacuumProjection else 0 := by
  rw [mul_smul_comm, smul_mul_assoc]
  have hs := congrArg (fun T : WordSpace I →L[ℂ] WordSpace I => t • T)
    (rightAnnihilation_semicircular_commutator i j)
  by_cases h : i = j
  · simpa only [smul_sub, h, ite_true] using hs
  · simp only [smul_sub, h, ite_false] at hs ⊢
    rw [hs]
    ext x
    simp

/-- Actual rank-one Duhamel formula for the entire complex-parameter exponential. -/
theorem rightAnnihilation_semicircular_exp_commutator (i j : I) (t : ℂ) :
    rightAnnihilation i * exp (t • semicircular j) -
      exp (t • semicircular j) * rightAnnihilation i =
      if i = j then
        t • (∫ u in (0 : ℝ)..1,
          exp ((1 - u) • (t • semicircular j)) * vacuumProjection *
            exp (u • (t • semicircular j))) else 0 := by
  rw [exponential_commutator_eq_integral, rightAnnihilation_scaled_semicircular_commutator]
  by_cases h : i = j
  · simp only [h, ite_true, mul_smul_comm, smul_mul_assoc]
    exact intervalIntegral.integral_smul t _
  · simp [h]

/-- Entire semicircular exponential IBP: the boundary rank-one operator splits the integral
into a product of actual vacuum exponential expectations. -/
theorem vacuumExpectation_semicircular_mul_semicircular_exp (i j : I) (t : ℂ) :
    vacuumExpectation (semicircular i * exp (t • semicircular j)) =
      if i = j then t * (∫ u in (0 : ℝ)..1,
        vacuumExpectation (exp ((1 - u) • (t • semicircular j))) *
          vacuumExpectation (exp (u • (t • semicircular j)))) else 0 := by
  rw [vacuumExpectation_semicircular_mul_exp,
    rightAnnihilation_scaled_semicircular_commutator]
  by_cases h : i = j
  · simp only [h, ite_true, mul_smul_comm, smul_mul_assoc]
    change (∫ u in (0 : ℝ)..1, vacuumLinear
      (t • (exp ((1 - u) • (t • semicircular j)) * vacuumProjection *
        exp (u • (t • semicircular j))))) = _
    simp only [map_smul, smul_eq_mul]
    change (∫ u in (0 : ℝ)..1, t * vacuumExpectation
      (exp ((1 - u) • (t • semicircular j)) * vacuumProjection *
        exp (u • (t • semicircular j)))) = _
    simp_rw [vacuumExpectation_mul_vacuumProjection_mul]
    exact intervalIntegral.integral_const_mul t _
  · simp [h, vacuumExpectation]

end FreeProbability.Fock

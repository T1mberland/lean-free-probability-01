import FreeProbability.Analytic.FockExponentialPolynomial
import FreeProbability.Analytic.FockResolventIntegrationByParts

/-!
# Actual polynomial resolvent integration by parts

The derivative is the existing polynomial tensor FDQ. The resolvent is the
actual inverse of `z-P(s)` at every point of its genuine resolvent set; no
exterior-series restriction or entrywise inverse is used.
-/

noncomputable section
open scoped Classical

namespace FreeProbability.Fock

variable {I : Type*}

/-- The inverse boundary derivative for every noncommutative polynomial at every actual
resolvent point, retaining both resolvent sandwich factors in the right order. -/
theorem rightAnnihilation_polynomial_resolvent_commutator
    (i : I) (p : WordPolynomial ℂ I) (z : ℂ)
    (hz : z ∈ resolventSet ℂ (evaluate semicircular p)) :
    operatorCommutator (rightAnnihilation i) (resolvent (evaluate semicircular p) z) =
      resolvent (evaluate semicircular p) z *
        polynomialRankOneInsertion (freeDifferenceQuotient i p) *
          resolvent (evaluate semicircular p) z := by
  have h := commutator_inverse_unit (rightAnnihilation i) hz.unit
  rw [← spectrum.resolvent_eq hz, hz.unit_spec] at h
  have hb : (algebraMap ℂ (WordSpace I →L[ℂ] WordSpace I) z - evaluate semicircular p) *
      rightAnnihilation i - rightAnnihilation i *
        (algebraMap ℂ (WordSpace I →L[ℂ] WordSpace I) z - evaluate semicircular p) =
      operatorCommutator (rightAnnihilation i) (evaluate semicircular p) := by
    simp only [operatorCommutator_apply, sub_mul, mul_sub, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    abel
  rw [hb, rightAnnihilation_polynomial_commutator] at h
  exact h

/-- Exact all-polynomial free resolvent IBP at every actual invertibility point. -/
theorem vacuumExpectation_polynomial_resolvent_integrationByParts
    (i : I) (p : WordPolynomial ℂ I) (z : ℂ)
    (hz : z ∈ resolventSet ℂ (evaluate semicircular p)) :
    vacuumExpectation (semicircular i * resolvent (evaluate semicircular p) z) =
      sandwichPolynomialExpectation (resolvent (evaluate semicircular p) z)
        (resolvent (evaluate semicircular p) z) (freeDifferenceQuotient i p) := by
  rw [← vacuumExpectation_rightAnnihilation_commutator]
  change vacuumExpectation
    (operatorCommutator (rightAnnihilation i) (resolvent (evaluate semicircular p) z)) = _
  rw [rightAnnihilation_polynomial_resolvent_commutator i p z hz,
    vacuumExpectation_sandwichRankOne]

end FreeProbability.Fock

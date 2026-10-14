import FreeProbability.Analytic.FockPolynomialResolvent
import FreeProbability.Analytic.FockExponentialCStar
import FreeProbability.Analytic.FockResolventCStar

/-! # Polynomial resolvent IBP in the actual faithful tracial C-star probability model -/

noncomputable section
open scoped Classical

namespace FreeProbability.Fock

variable {I : Type*}

/-- Spectral permanence identifies the entire intrinsic and bounded-operator polynomial domains. -/
theorem polynomial_mem_resolventSet_iff (p : WordPolynomial ℂ I) (z : ℂ) :
    z ∈ resolventSet ℂ (evaluate closedSemicircular p) ↔
      z ∈ resolventSet ℂ (evaluate semicircular p) := by
  have h := not_iff_not.mp (StarSubalgebra.mem_spectrum_iff (closedSemicircularAlgebra I)
    (a := evaluate closedSemicircular p) (z := z))
  change z ∈ resolventSet ℂ (evaluate closedSemicircular p) ↔
    z ∈ resolventSet ℂ ((closedSemicircularAlgebra I).val (evaluate closedSemicircular p)) at h
  rwa [coe_evaluate_closedSemicircular] at h

/-- The intrinsic polynomial resolvent is the actual operator inverse under inclusion. -/
theorem polynomial_resolvent_coe (p : WordPolynomial ℂ I) (z : ℂ)
    (hz : z ∈ resolventSet ℂ (evaluate closedSemicircular p)) :
    (closedSemicircularAlgebra I).subtype.toAlgHom (resolvent (evaluate closedSemicircular p) z) =
      resolvent (evaluate semicircular p) z := by
  change (closedSemicircularAlgebra I).subtype.toAlgHom
    (Ring.inverse (algebraMap ℂ _ z - evaluate closedSemicircular p)) = _
  have h := algHom_map_ringInverse_of_isUnit
    (closedSemicircularAlgebra I).subtype.toAlgHom hz
  simp only [map_sub, AlgHom.commutes] at h
  change (closedSemicircularAlgebra I).subtype.toAlgHom
    (Ring.inverse (algebraMap ℂ _ z - evaluate closedSemicircular p)) =
      Ring.inverse (algebraMap ℂ _ z -
        (closedSemicircularAlgebra I).val (evaluate closedSemicircular p)) at h
  rwa [coe_evaluate_closedSemicircular] at h

/-- Full-domain all-polynomial resolvent IBP inside the actual faithful tracial closed C-star model. -/
theorem closedGeneratedVacuumState_polynomial_resolvent_integrationByParts
    (i : I) (p : WordPolynomial ℂ I) (z : ℂ)
    (hz : z ∈ resolventSet ℂ (evaluate closedSemicircular p)) :
    (closedGeneratedVacuumState I).expectation
      (closedSemicircular i * resolvent (evaluate closedSemicircular p) z) =
      closedSandwichPolynomialExpectation (resolvent (evaluate closedSemicircular p) z)
        (resolvent (evaluate closedSemicircular p) z) (freeDifferenceQuotient i p) := by
  change vacuumExpectation ((closedSemicircularAlgebra I).subtype.toAlgHom
    (closedSemicircular i * resolvent (evaluate closedSemicircular p) z)) = _
  rw [map_mul, polynomial_resolvent_coe p z hz, closedSandwichPolynomialExpectation_eq]
  change vacuumExpectation (semicircular i * resolvent (evaluate semicircular p) z) =
    sandwichPolynomialExpectation
      ((closedSemicircularAlgebra I).subtype.toAlgHom (resolvent (evaluate closedSemicircular p) z))
      ((closedSemicircularAlgebra I).subtype.toAlgHom (resolvent (evaluate closedSemicircular p) z))
      (freeDifferenceQuotient i p)
  rw [polynomial_resolvent_coe p z hz]
  exact vacuumExpectation_polynomial_resolvent_integrationByParts i p z
    ((polynomial_mem_resolventSet_iff p z).mp hz)

end FreeProbability.Fock

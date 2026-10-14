import FreeProbability.Fock.CatalanMoments
import FreeProbability.Algebraic.SemicircularCumulants
import FreeProbability.Algebraic.UnivariateCumulant
import FreeProbability.Combinatorics.PairingCumulantShape

/-!
# Actual Fock semicircular cumulants

Uniqueness of moment–cumulant inversion identifies the cumulants of the
constructed operators. No semicircular-cumulant realization is assumed.
-/

namespace FreeProbability.Fock

variable {I : Type*}

/-- The actual generator in the faithful tracial C-star model has only its
unit second cumulant nonzero. -/
theorem closedSemicircular_hasSemicircularCumulants (i : I) :
    HasSemicircularCumulants (closedGeneratedVacuumState I).toProbabilitySpace
      (closedSemicircular i) 1 := by
  let φ := (closedGeneratedVacuumState I).toProbabilitySpace
  let s := closedSemicircular i
  let M : List Unit → ℂ := fun w => φ.expectation (s ^ w.length)
  let K : List Unit → ℂ := pairingCumulantShape 1
  have hK : K = freeCumulant M := by
    apply freeCumulant_unique_of_moment_formula M K
    · simp [K, pairingCumulantShape]
    · intro w _hw
      rw [sum_partitionContribution_pairingCumulantShape]
      simp only [one_pow, mul_one]
      change vacuumExpectation ((closedSemicircularAlgebra I).val
        (closedSemicircular i ^ w.length)) = _
      rw [map_pow]
      exact vacuumExpectation_semicircular_pow_eq_pairingCard i w.length
  intro n
  have h := congrFun hK (List.replicate n ())
  simp only [K, M, pairingCumulantShape, List.length_replicate,
    freeCumulant_powerMoments] at h
  exact h.symm

end FreeProbability.Fock

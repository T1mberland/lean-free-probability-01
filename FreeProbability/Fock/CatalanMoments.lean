import FreeProbability.Fock.WickFormula
import FreeProbability.Combinatorics.NoncrossingPairingCatalan

/-!
# The genuine Fock semicircular generators have Catalan moments

These are moments of the already constructed bounded self-adjoint operators,
with their actual faithful tracial vacuum restriction. The spectral probability
measure and its semicircle density identification remain analytic obligations.
-/

noncomputable section
open scoped Classical
open FreeProbability.NoncrossingPairing

namespace FreeProbability.Fock

variable {I : Type*}

/-- Every even moment of a canonical generator is a Catalan number. -/
theorem vacuumExpectation_semicircular_even (i : I) (n : ℕ) :
    vacuumExpectation (semicircular i ^ (2 * n)) = (catalan n : ℂ) := by
  rw [vacuumExpectation_semicircular_pow_eq_pairingCard, card_even_eq_catalan]

/-- Every odd moment vanishes. -/
theorem vacuumExpectation_semicircular_odd (i : I) (n : ℕ) :
    vacuumExpectation (semicircular i ^ (2 * n + 1)) = 0 := by
  rw [vacuumExpectation_semicircular_pow_eq_pairingCard,
    card_eq_zero_of_odd (show Odd (2 * n + 1) from ⟨n, by omega⟩)]
  simp

/-- The complete moment sequence of the actual canonical generator. -/
theorem vacuumExpectation_semicircular_pow (i : I) (n : ℕ) :
    vacuumExpectation (semicircular i ^ n) = if Even n then (catalan (n / 2) : ℂ) else 0 := by
  rw [vacuumExpectation_semicircular_pow_eq_pairingCard, card_eq_catalan_or_zero]
  split <;> simp

/-- Catalan even moments in the faithful tracial C-star probability space itself. -/
theorem closedGeneratedVacuumState_even (i : I) (n : ℕ) :
    (closedGeneratedVacuumState I).expectation (closedSemicircular i ^ (2 * n)) = (catalan n : ℂ) := by
  change vacuumExpectation ((closedSemicircularAlgebra I).val (closedSemicircular i ^ (2 * n))) = _
  rw [map_pow]
  exact vacuumExpectation_semicircular_even i n

/-- Vanishing odd moments in the faithful tracial C-star probability space itself. -/
theorem closedGeneratedVacuumState_odd (i : I) (n : ℕ) :
    (closedGeneratedVacuumState I).expectation (closedSemicircular i ^ (2 * n + 1)) = 0 := by
  change vacuumExpectation ((closedSemicircularAlgebra I).val (closedSemicircular i ^ (2 * n + 1))) = 0
  rw [map_pow]
  exact vacuumExpectation_semicircular_odd i n

/-- A concrete fourth-moment usage of the all-order Catalan theorem. -/
example (i : I) : (closedGeneratedVacuumState I).expectation (closedSemicircular i ^ 4) = 2 := by
  simpa [catalan_two] using closedGeneratedVacuumState_even i 2

/-- A concrete sixth-moment usage. -/
example (i : I) : (closedGeneratedVacuumState I).expectation (closedSemicircular i ^ 6) = 5 := by
  simpa [catalan_three] using closedGeneratedVacuumState_even i 3

end FreeProbability.Fock

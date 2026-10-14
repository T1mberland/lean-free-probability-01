import FreeProbability.Analytic.FockAnalyticSeriesCore
import FreeProbability.Analytic.FockExponentialPolynomial

/-!
# Norm-convergent polynomial analytic series integration by parts

Both value and derivative norm bounds are explicit. The derivative series is
proved convergent, and every cut contracts the actual existing tensor FDQ of
the original polynomial, preserving the order of both power factors.
-/

noncomputable section
open scoped Classical

namespace FreeProbability.Fock

variable {I : Type*}

/-- The actual vacuum witnesses that word Fock space is nontrivial. -/
local instance : Nontrivial (WordSpace I) := ⟨⟨vacuum, 0, by
  intro h
  have hn := norm_vacuum (I := I)
  rw [h, norm_zero] at hn
  norm_num at hn⟩⟩

/-- The exact ordered tensor-FDQ cut contraction for degree `n+1` in the polynomial. -/
def analyticPolynomialDerivativeTerm (i : I) (p : WordPolynomial ℂ I) (n : ℕ) : ℂ :=
  ∑ k : Fin (n + 1), sandwichPolynomialExpectation
    (evaluate semicircular p ^ k.val) (evaluate semicircular p ^ (n - k.val))
    (freeDifferenceQuotient i p)

/-- Vacuum evaluation of every actual insertion is exactly the tensor derivative contraction. -/
theorem vacuumExpectation_analyticPowerInsertion (i : I) (p : WordPolynomial ℂ I) (n : ℕ) :
    vacuumExpectation (analyticPowerInsertion (evaluate semicircular p)
      (polynomialRankOneInsertion (freeDifferenceQuotient i p)) n) =
      analyticPolynomialDerivativeTerm i p n := by
  change vacuumLinear (∑ k : Fin (n + 1), _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact vacuumExpectation_sandwichRankOne _ _ _

/-- The explicit scalar derivative bound comes from the actual bounded rank-one insertion. -/
theorem norm_analyticPolynomialDerivativeTerm_le (i : I) (p : WordPolynomial ℂ I) (n : ℕ) :
    ‖analyticPolynomialDerivativeTerm i p n‖ ≤
      (n + 1 : ℝ) * ‖evaluate semicircular p‖ ^ n *
        ‖polynomialRankOneInsertion (freeDifferenceQuotient i p)‖ := by
  rw [← vacuumExpectation_analyticPowerInsertion]
  exact (norm_vacuumExpectation_le _).trans (norm_analyticPowerInsertion_le _ _ _)

/-- The tensor-FDQ contraction series is absolutely summable under the explicit derivative bound. -/
theorem summable_norm_analyticPolynomialDerivative (i : I) (p : WordPolynomial ℂ I) (c : ℕ → ℂ)
    (hd : Summable (fun n : ℕ => (n + 1 : ℝ) * ‖c (n + 1)‖ * ‖evaluate semicircular p‖ ^ n)) :
    Summable (fun n => ‖c (n + 1) * analyticPolynomialDerivativeTerm i p n‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (hd.mul_right ‖polynomialRankOneInsertion (freeDifferenceQuotient i p)‖)
  intro n
  rw [norm_mul]
  calc
    _ ≤ ‖c (n + 1)‖ * ((n + 1 : ℝ) * ‖evaluate semicircular p‖ ^ n *
        ‖polynomialRankOneInsertion (freeDifferenceQuotient i p)‖) :=
      mul_le_mul_of_nonneg_left (norm_analyticPolynomialDerivativeTerm_le i p n) (norm_nonneg _)
    _ = _ := by ring

/-- The derivative bound gives norm convergence of the actual scalar tensor-FDQ cut series. -/
theorem summable_analyticPolynomialDerivative (i : I) (p : WordPolynomial ℂ I) (c : ℕ → ℂ)
    (hd : Summable (fun n : ℕ => (n + 1 : ℝ) * ‖c (n + 1)‖ * ‖evaluate semicircular p‖ ^ n)) :
    Summable (fun n => c (n + 1) * analyticPolynomialDerivativeTerm i p n) := by
  have hs := (vacuumContinuous I).summable
    (summable_analyticInsertionSeries c (evaluate semicircular p)
      (polynomialRankOneInsertion (freeDifferenceQuotient i p)) hd)
  convert hs using 1
  funext n
  change c (n + 1) * analyticPolynomialDerivativeTerm i p n =
    vacuumLinear (c (n + 1) • analyticPowerInsertion (evaluate semicircular p)
      (polynomialRankOneInsertion (freeDifferenceQuotient i p)) n)
  rw [map_smul]
  change _ = c (n + 1) * vacuumExpectation (analyticPowerInsertion _ _ n)
  rw [vacuumExpectation_analyticPowerInsertion]

/-- Genuine norm-convergent analytic-series IBP for every noncommutative polynomial,
under explicit absolute bounds on both values and ordered derivatives. -/
theorem vacuumExpectation_polynomial_analyticSeries_integrationByParts
    (i : I) (p : WordPolynomial ℂ I) (c : ℕ → ℂ)
    (hv : Summable (fun n => ‖c n‖ * ‖evaluate semicircular p‖ ^ n))
    (hd : Summable (fun n : ℕ => (n + 1 : ℝ) * ‖c (n + 1)‖ * ‖evaluate semicircular p‖ ^ n)) :
    vacuumExpectation (semicircular i * analyticSeries c (evaluate semicircular p)) =
      ∑' n, c (n + 1) * analyticPolynomialDerivativeTerm i p n := by
  rw [← vacuumExpectation_rightAnnihilation_commutator]
  change vacuumExpectation (analyticCommutator (rightAnnihilation i)
    (analyticSeries c (evaluate semicircular p))) = _
  rw [analyticSeries_commutator c (rightAnnihilation i) (evaluate semicircular p) hv]
  have hb : analyticCommutator (rightAnnihilation i) (evaluate semicircular p) =
      polynomialRankOneInsertion (freeDifferenceQuotient i p) :=
    rightAnnihilation_polynomial_commutator i p
  rw [hb]
  change vacuumContinuous I (∑' n, c (n + 1) • analyticPowerInsertion
    (evaluate semicircular p) (polynomialRankOneInsertion (freeDifferenceQuotient i p)) n) = _
  rw [(vacuumContinuous I).map_tsum
    (summable_analyticInsertionSeries c (evaluate semicircular p)
      (polynomialRankOneInsertion (freeDifferenceQuotient i p)) hd)]
  apply tsum_congr
  intro n
  change vacuumLinear (c (n + 1) • analyticPowerInsertion _ _ n) = _
  rw [map_smul]
  change c (n + 1) * vacuumExpectation (analyticPowerInsertion _ _ n) = _
  rw [vacuumExpectation_analyticPowerInsertion]

end FreeProbability.Fock

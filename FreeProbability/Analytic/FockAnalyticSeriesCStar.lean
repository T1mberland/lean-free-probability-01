import FreeProbability.Analytic.FockAnalyticSeriesPolynomial
import FreeProbability.Analytic.FockExponentialCStar

/-! # Norm-convergent analytic-series IBP in the actual faithful tracial closed C-star model -/

noncomputable section
open scoped Classical

namespace FreeProbability.Fock

variable {I : Type*}

local instance : Nontrivial (closedSemicircularAlgebra I) :=
  (closedGeneratedVacuumState I).toProbabilitySpace.nontrivial

/-- The actual continuous complex-linear inclusion of the closed C-star algebra into operators. -/
def analyticClosedInclusion : closedSemicircularAlgebra I →L[ℂ] (WordSpace I →L[ℂ] WordSpace I) where
  toLinearMap := (closedSemicircularAlgebra I).subtype.toAlgHom.toLinearMap
  cont := continuous_subtype_val

/-- Evaluation preserves the actual norm under the closed generated-algebra inclusion. -/
theorem norm_evaluate_closedSemicircular (p : WordPolynomial ℂ I) :
    ‖evaluate closedSemicircular p‖ = ‖evaluate semicircular p‖ := by
  rw [← coe_evaluate_closedSemicircular]
  rfl

/-- The intrinsic convergent C-star series is precisely the actual operator series under inclusion. -/
theorem analyticClosedInclusion_series (p : WordPolynomial ℂ I) (c : ℕ → ℂ)
    (hv : Summable (fun n => ‖c n‖ * ‖evaluate closedSemicircular p‖ ^ n)) :
    analyticClosedInclusion (analyticSeries c (evaluate closedSemicircular p)) =
      analyticSeries c (evaluate semicircular p) := by
  rw [analyticSeries, (analyticClosedInclusion (I := I)).map_tsum
    (summable_analyticSeries c (evaluate closedSemicircular p) hv)]
  apply tsum_congr
  intro n
  change (closedSemicircularAlgebra I).subtype.toAlgHom
    (c n • evaluate closedSemicircular p ^ n) = c n • evaluate semicircular p ^ n
  rw [map_smul, map_pow]
  change c n • (closedSemicircularAlgebra I).val (evaluate closedSemicircular p) ^ n = _
  rw [coe_evaluate_closedSemicircular]

/-- Ordered tensor-FDQ power cuts using the actual faithful tracial C-star state itself. -/
def closedAnalyticPolynomialDerivativeTerm (i : I) (p : WordPolynomial ℂ I) (n : ℕ) : ℂ :=
  ∑ k : Fin (n + 1), closedSandwichPolynomialExpectation
    (evaluate closedSemicircular p ^ k.val) (evaluate closedSemicircular p ^ (n - k.val))
    (freeDifferenceQuotient i p)

/-- The intrinsic cut contraction agrees with its actual concrete operator vacuum contraction. -/
theorem closedAnalyticPolynomialDerivativeTerm_eq (i : I) (p : WordPolynomial ℂ I) (n : ℕ) :
    closedAnalyticPolynomialDerivativeTerm i p n = analyticPolynomialDerivativeTerm i p n := by
  apply Finset.sum_congr rfl
  intro k hk
  rw [closedSandwichPolynomialExpectation_eq]
  rw [map_pow, map_pow, coe_evaluate_closedSemicircular]

/-- The explicit intrinsic derivative bound proves absolute convergence of the actual closed-state cuts. -/
theorem summable_norm_closedAnalyticPolynomialDerivative
    (i : I) (p : WordPolynomial ℂ I) (c : ℕ → ℂ)
    (hd : Summable (fun n : ℕ => (n + 1 : ℝ) * ‖c (n + 1)‖ * ‖evaluate closedSemicircular p‖ ^ n)) :
    Summable (fun n => ‖c (n + 1) * closedAnalyticPolynomialDerivativeTerm i p n‖) := by
  have hd' : Summable (fun n : ℕ => (n + 1 : ℝ) * ‖c (n + 1)‖ * ‖evaluate semicircular p‖ ^ n) := by
    simpa only [norm_evaluate_closedSemicircular] using hd
  simpa only [closedAnalyticPolynomialDerivativeTerm_eq] using
    summable_norm_analyticPolynomialDerivative i p c hd'

/-- Genuine norm-convergent analytic IBP inside the literal faithful tracial C-star probability space,
with both explicit value and derivative norm bounds and its own tensor-FDQ cut contraction. -/
theorem closedGeneratedVacuumState_polynomial_analyticSeries_integrationByParts
    (i : I) (p : WordPolynomial ℂ I) (c : ℕ → ℂ)
    (hv : Summable (fun n => ‖c n‖ * ‖evaluate closedSemicircular p‖ ^ n))
    (hd : Summable (fun n : ℕ => (n + 1 : ℝ) * ‖c (n + 1)‖ * ‖evaluate closedSemicircular p‖ ^ n)) :
    (closedGeneratedVacuumState I).expectation
      (closedSemicircular i * analyticSeries c (evaluate closedSemicircular p)) =
      ∑' n, c (n + 1) * closedAnalyticPolynomialDerivativeTerm i p n := by
  change vacuumExpectation ((closedSemicircularAlgebra I).subtype.toAlgHom
    (closedSemicircular i * analyticSeries c (evaluate closedSemicircular p))) = _
  rw [map_mul]
  change vacuumExpectation (semicircular i *
    analyticClosedInclusion (analyticSeries c (evaluate closedSemicircular p))) = _
  rw [analyticClosedInclusion_series p c hv]
  simp_rw [closedAnalyticPolynomialDerivativeTerm_eq]
  have hv' : Summable (fun n => ‖c n‖ * ‖evaluate semicircular p‖ ^ n) := by
    simpa only [norm_evaluate_closedSemicircular] using hv
  have hd' : Summable (fun n : ℕ => (n + 1 : ℝ) * ‖c (n + 1)‖ * ‖evaluate semicircular p‖ ^ n) := by
    simpa only [norm_evaluate_closedSemicircular] using hd
  exact vacuumExpectation_polynomial_analyticSeries_integrationByParts i p c hv' hd'

end FreeProbability.Fock

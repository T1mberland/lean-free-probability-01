import FreeProbability.Analytic.FockAnalyticSeriesPolynomial
import FreeProbability.Analytic.FockExponentialMatrix

/-!
# Genuine finite-matrix analytic-series integration by parts

The series is evaluated in the actual complete matrix Banach algebra. The
explicit value and derivative norm bounds justify its sums. The amplified
FDQ cuts retain both matrix indices, and use the actual entrywise vacuum state.
-/

noncomputable section
open scoped Classical Matrix.Norms.Operator

namespace FreeProbability.Fock

variable {I N : Type*} [Fintype N] [DecidableEq N]

local instance : Nontrivial (WordSpace I) := ⟨⟨vacuum, 0, by
  intro h
  have hn := norm_vacuum (I := I)
  rw [h, norm_zero] at hn
  norm_num at hn⟩⟩

local instance : NormedAddCommGroup (Matrix N N (WordSpace I →L[ℂ] WordSpace I)) :=
  { Matrix.linftyOpNormedRing (α := WordSpace I →L[ℂ] WordSpace I) (n := N) with }

local instance : @CompleteSpace (Matrix N N (WordSpace I →L[ℂ] WordSpace I))
    (Matrix.linftyOpNormedRing.toUniformSpace) := by
  change CompleteSpace (N → N → (WordSpace I →L[ℂ] WordSpace I))
  infer_instance

/-- Actual matrix rank-one insertion of its entrywise polynomial tensor derivative. -/
def matrixAnalyticRankOneInsertion (Z : Matrix N N (PolynomialTensor ℂ I)) :
    Matrix N N (WordSpace I →L[ℂ] WordSpace I) := fun r c => polynomialRankOneInsertion (Z r c)

omit [DecidableEq N] in
/-- Exact ordered amplified vacuum factorization of each matrix tensor sandwich. -/
theorem matrixAnalytic_vacuum_sandwich
    (L R : Matrix N N (WordSpace I →L[ℂ] WordSpace I))
    (Z : Matrix N N (PolynomialTensor ℂ I)) (r c : N) :
    vacuumExpectation ((L * matrixAnalyticRankOneInsertion Z * R) r c) =
      matrixExponentialTensorContraction L R Z r c := by
  change vacuumLinear ((L * matrixAnalyticRankOneInsertion Z * R) r c) = _
  simp only [Matrix.mul_apply]
  simp only [matrixAnalyticRankOneInsertion, Finset.sum_mul, map_sum]
  change (∑ l, ∑ k, vacuumExpectation (L r k * polynomialRankOneInsertion (Z k l) * R l c)) = _
  simp_rw [vacuumExpectation_sandwichRankOne]
  rw [Finset.sum_comm]
  rfl

/-- The complete ordered tensor derivative cuts of degree `n+1` in the matrix polynomial. -/
def matrixAnalyticDerivativeTerm (i : I) (P : Matrix N N (WordPolynomial ℂ I))
    (r c : N) (n : ℕ) : ℂ :=
  ∑ k : Fin (n + 1), matrixExponentialTensorContraction
    (matrixPolynomialEvaluate semicircular P ^ k.val)
    (matrixPolynomialEvaluate semicircular P ^ (n - k.val))
    (matrixFreeDifferenceQuotient i P) r c

/-- Actual matrix insertion powers evaluate to the full ordered tensor derivative cut contraction. -/
theorem matrixAnalytic_powerInsertion_vacuum
    (i : I) (P : Matrix N N (WordPolynomial ℂ I)) (r c : N) (n : ℕ) :
    matrixEntryVacuum (I := I) r c
      (analyticPowerInsertion (matrixPolynomialEvaluate semicircular P)
        (matrixAnalyticRankOneInsertion (matrixFreeDifferenceQuotient i P)) n) =
      matrixAnalyticDerivativeTerm i P r c n := by
  change matrixEntryVacuum (I := I) r c (∑ k : Fin (n + 1), _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact matrixAnalytic_vacuum_sandwich _ _ _ r c

/-- Each actual operator entry is bounded by the complete matrix operator norm. -/
theorem matrixAnalytic_norm_entry_le (M : Matrix N N (WordSpace I →L[ℂ] WordSpace I)) (r c : N) :
    ‖M r c‖ ≤ ‖M‖ := by
  have h : ‖M r c‖₊ ≤ ‖M‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    exact (Finset.single_le_sum (fun j _ => (show 0 ≤ ‖M r j‖₊ from zero_le)) (Finset.mem_univ c)).trans
      (Finset.le_sup (f := fun i : N => ∑ j, ‖M i j‖₊) (Finset.mem_univ r))
  exact_mod_cast h

/-- The actual amplified vacuum entry has norm bound one in the complete matrix Banach algebra. -/
theorem matrixAnalytic_norm_entryVacuum_le
    (M : Matrix N N (WordSpace I →L[ℂ] WordSpace I)) (r c : N) :
    ‖matrixEntryVacuum (I := I) r c M‖ ≤ ‖M‖ :=
  (norm_vacuumExpectation_le _).trans (matrixAnalytic_norm_entry_le M r c)

/-- An explicit amplified derivative bound uses the actual matrix-entry state norm bound one. -/
theorem norm_matrixAnalyticDerivativeTerm_le
    (i : I) (P : Matrix N N (WordPolynomial ℂ I)) (r c : N) (n : ℕ) :
    ‖matrixAnalyticDerivativeTerm i P r c n‖ ≤ (n + 1 : ℝ) *
      ‖matrixPolynomialEvaluate semicircular P‖ ^ n *
        ‖matrixAnalyticRankOneInsertion (matrixFreeDifferenceQuotient i P)‖ := by
  let : Nonempty N := ⟨r⟩
  rw [← matrixAnalytic_powerInsertion_vacuum]
  exact (matrixAnalytic_norm_entryVacuum_le _ r c).trans (norm_analyticPowerInsertion_le _ _ _)

/-- Absolute convergence of the amplified FDQ cut series follows from the explicit derivative bound. -/
theorem summable_norm_matrixAnalyticDerivative
    (i : I) (P : Matrix N N (WordPolynomial ℂ I)) (r c : N) (a : ℕ → ℂ)
    (hd : Summable (fun n : ℕ => (n + 1 : ℝ) * ‖a (n + 1)‖ *
      ‖matrixPolynomialEvaluate semicircular P‖ ^ n)) :
    Summable (fun n => ‖a (n + 1) * matrixAnalyticDerivativeTerm i P r c n‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (hd.mul_right ‖matrixAnalyticRankOneInsertion (matrixFreeDifferenceQuotient i P)‖)
  intro n
  rw [norm_mul]
  calc
    _ ≤ ‖a (n + 1)‖ * ((n + 1 : ℝ) * ‖matrixPolynomialEvaluate semicircular P‖ ^ n *
        ‖matrixAnalyticRankOneInsertion (matrixFreeDifferenceQuotient i P)‖) :=
      mul_le_mul_of_nonneg_left (norm_matrixAnalyticDerivativeTerm_le i P r c n) (norm_nonneg _)
    _ = _ := by ring

/-- The explicit derivative bound proves convergence of the actual amplified tensor-FDQ cut series. -/
theorem summable_matrixAnalyticDerivative
    (i : I) (P : Matrix N N (WordPolynomial ℂ I)) (r c : N) (a : ℕ → ℂ)
    (hd : Summable (fun n : ℕ => (n + 1 : ℝ) * ‖a (n + 1)‖ *
      ‖matrixPolynomialEvaluate semicircular P‖ ^ n)) :
    Summable (fun n => a (n + 1) * matrixAnalyticDerivativeTerm i P r c n) := by
  let : Nonempty N := ⟨r⟩
  have hs := (matrixEntryVacuum (I := I) r c).summable
    (summable_analyticInsertionSeries a (matrixPolynomialEvaluate semicircular P)
      (matrixAnalyticRankOneInsertion (matrixFreeDifferenceQuotient i P)) hd)
  convert hs using 1
  funext n
  rw [map_smul]
  change _ = a (n + 1) * matrixEntryVacuum (I := I) r c (analyticPowerInsertion _ _ n)
  rw [matrixAnalytic_powerInsertion_vacuum]

/-- Genuine full-matrix norm-convergent analytic-series IBP under explicit value and derivative bounds. -/
theorem vacuumState_matrixPolynomial_analyticSeries_integrationByParts
    (i : I) (P : Matrix N N (WordPolynomial ℂ I)) (a : ℕ → ℂ) (r c : N)
    (hv : Summable (fun n => ‖a n‖ * ‖matrixPolynomialEvaluate semicircular P‖ ^ n))
    (hd : Summable (fun n : ℕ => (n + 1 : ℝ) * ‖a (n + 1)‖ *
      ‖matrixPolynomialEvaluate semicircular P‖ ^ n)) :
    ((Matrix.diagonal (fun _ : N => semicircular i) *
        analyticSeries a (matrixPolynomialEvaluate semicircular P)).map vacuumExpectation) r c =
      ∑' n, a (n + 1) * matrixAnalyticDerivativeTerm i P r c n := by
  let : Nonempty N := ⟨r⟩
  let X := matrixPolynomialEvaluate semicircular P
  let C := Matrix.diagonal (fun _ : N => rightAnnihilation i)
  have hb : analyticCommutator C X =
      matrixAnalyticRankOneInsertion (matrixFreeDifferenceQuotient i P) := by
    have h := matrix_polynomial_commutator i P (1 : ℂ)
    simp only [one_smul] at h
    exact h
  have h := analyticSeries_commutator a C X hv
  rw [hb] at h
  have he := congrArg (matrixEntryVacuum (I := I) r c) h
  have hs := summable_analyticInsertionSeries a X
    (matrixAnalyticRankOneInsertion (matrixFreeDifferenceQuotient i P)) hd
  have he' := he.trans ((matrixEntryVacuum (I := I) r c).map_tsum hs)
  change vacuumExpectation ((C * analyticSeries a X - analyticSeries a X * C) r c) = _ at he'
  simp only [C, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal] at he'
  rw [vacuumExpectation_rightAnnihilation_commutator] at he'
  simp only [Matrix.map_apply, Matrix.diagonal_mul]
  change vacuumExpectation (semicircular i * (analyticSeries a X) r c) = _
  rw [he']
  apply tsum_congr
  intro n
  rw [map_smul]
  change a (n + 1) * matrixEntryVacuum (I := I) r c (analyticPowerInsertion _ _ n) = _
  rw [matrixAnalytic_powerInsertion_vacuum]

end FreeProbability.Fock

import FreeProbability.Analytic.FockAnalyticSeriesMatrix
import FreeProbability.Analytic.FockAnalyticSeriesCStar
import FreeProbability.OperatorValued.MatrixExpectation

/-! # Genuine norm-convergent amplified analytic IBP in the faithful tracial C-star model -/

noncomputable section
open scoped Classical Matrix.Norms.Operator

namespace FreeProbability.Fock

variable {I N : Type*} [Fintype N] [DecidableEq N]

local instance : Nontrivial (closedSemicircularAlgebra I) :=
  (closedGeneratedVacuumState I).toProbabilitySpace.nontrivial

local instance : Nontrivial (WordSpace I) := ⟨⟨vacuum, 0, by
  intro h
  have hn := norm_vacuum (I := I)
  rw [h, norm_zero] at hn
  norm_num at hn⟩⟩

local instance : NormedAddCommGroup (Matrix N N (WordSpace I →L[ℂ] WordSpace I)) :=
  { Matrix.linftyOpNormedRing (α := WordSpace I →L[ℂ] WordSpace I) (n := N) with }
local instance : NormedAddCommGroup (Matrix N N (closedSemicircularAlgebra I)) :=
  { Matrix.linftyOpNormedRing (α := closedSemicircularAlgebra I) (n := N) with }

local instance : @CompleteSpace (Matrix N N (WordSpace I →L[ℂ] WordSpace I))
    (Matrix.linftyOpNormedRing.toUniformSpace) := by
  change CompleteSpace (N → N → (WordSpace I →L[ℂ] WordSpace I))
  infer_instance
local instance : @CompleteSpace (Matrix N N (closedSemicircularAlgebra I))
    (Matrix.linftyOpNormedRing.toUniformSpace) := by
  change CompleteSpace (N → N → closedSemicircularAlgebra I)
  infer_instance

/-- The actual continuous matrix inclusion into bounded-operator matrices. -/
def analyticClosedMatrixInclusion : Matrix N N (closedSemicircularAlgebra I) →L[ℂ]
    Matrix N N (WordSpace I →L[ℂ] WordSpace I) where
  toLinearMap := (closedSemicircularAlgebra I).subtype.toAlgHom.mapMatrix.toLinearMap
  cont := continuous_matrix fun r c =>
    (analyticClosedInclusion (I := I)).continuous.comp (continuous_apply_apply r c)

/-- Intrinsic and operator matrix polynomial evaluations have exactly the same Banach norm. -/
theorem norm_matrixEvaluate_closedSemicircular (P : Matrix N N (WordPolynomial ℂ I)) :
    ‖matrixPolynomialEvaluate closedSemicircular P‖ = ‖matrixPolynomialEvaluate semicircular P‖ := by
  have h : ‖matrixPolynomialEvaluate closedSemicircular P‖₊ =
      ‖matrixPolynomialEvaluate semicircular P‖₊ := by
    rw [Matrix.linfty_opNNNorm_def, Matrix.linfty_opNNNorm_def]
    apply Finset.sup_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro c hc
    change ‖evaluate closedSemicircular (P r c)‖₊ = ‖evaluate semicircular (P r c)‖₊
    exact NNReal.eq (norm_evaluate_closedSemicircular (P r c))
  exact congrArg (fun x : NNReal => (x : ℝ)) h

/-- The intrinsic actual matrix series is preserved by the actual continuous algebra inclusion. -/
theorem analyticClosedMatrixInclusion_series (P : Matrix N N (WordPolynomial ℂ I)) (a : ℕ → ℂ)
    (hv : Summable (fun n => ‖a n‖ * ‖matrixPolynomialEvaluate closedSemicircular P‖ ^ n)) :
    analyticClosedMatrixInclusion (analyticSeries a (matrixPolynomialEvaluate closedSemicircular P)) =
      analyticSeries a (matrixPolynomialEvaluate semicircular P) := by
  rcases isEmpty_or_nonempty N with hN | hN
  · let : IsEmpty N := hN
    exact Subsingleton.elim _ _
  · let : Nonempty N := hN
    have he := (analyticClosedMatrixInclusion (I := I) (N := N)).map_tsum
      (summable_analyticSeries a (matrixPolynomialEvaluate closedSemicircular P) hv)
    apply he.trans
    apply tsum_congr
    intro n
    change (closedSemicircularAlgebra I).subtype.toAlgHom.mapMatrix
      (a n • matrixPolynomialEvaluate closedSemicircular P ^ n) =
        a n • matrixPolynomialEvaluate semicircular P ^ n
    rw [map_smul, map_pow]
    congr 2
    apply Matrix.ext
    intro r c
    exact coe_evaluate_closedSemicircular (P r c)

/-- Intrinsic actual matrix series entries are transported from the whole matrix series. -/
theorem analyticClosedMatrixInclusion_series_entry
    (P : Matrix N N (WordPolynomial ℂ I)) (a : ℕ → ℂ)
    (hv : Summable (fun n => ‖a n‖ * ‖matrixPolynomialEvaluate closedSemicircular P‖ ^ n)) (r c : N) :
    (closedSemicircularAlgebra I).subtype.toAlgHom
      ((analyticSeries a (matrixPolynomialEvaluate closedSemicircular P)) r c) =
      (analyticSeries a (matrixPolynomialEvaluate semicircular P)) r c :=
  congrArg (fun X => X r c) (analyticClosedMatrixInclusion_series P a hv)

/-- Ordered amplified power cuts using the actual faithful tracial C-star state itself. -/
def closedMatrixAnalyticDerivativeTerm
    (i : I) (P : Matrix N N (WordPolynomial ℂ I)) (r c : N) (n : ℕ) : ℂ :=
  ∑ k : Fin (n + 1), ∑ s, ∑ t, closedSandwichPolynomialExpectation
    ((matrixPolynomialEvaluate closedSemicircular P ^ k.val) r s)
    ((matrixPolynomialEvaluate closedSemicircular P ^ (n - k.val)) t c)
    (matrixFreeDifferenceQuotient i P s t)

/-- Intrinsic full-matrix tensor-FDQ cuts agree with the concrete operator-matrix vacuum cuts. -/
theorem closedMatrixAnalyticDerivativeTerm_eq
    (i : I) (P : Matrix N N (WordPolynomial ℂ I)) (r c : N) (n : ℕ) :
    closedMatrixAnalyticDerivativeTerm i P r c n = matrixAnalyticDerivativeTerm i P r c n := by
  have hp (m : ℕ) :
      (closedSemicircularAlgebra I).subtype.toAlgHom.mapMatrix
        (matrixPolynomialEvaluate closedSemicircular P ^ m) =
          matrixPolynomialEvaluate semicircular P ^ m := by
    rw [map_pow]
    congr 1
    apply Matrix.ext
    intro r c
    exact coe_evaluate_closedSemicircular (P r c)
  have he (m : ℕ) (r c : N) : (closedSemicircularAlgebra I).subtype.toAlgHom
      ((matrixPolynomialEvaluate closedSemicircular P ^ m) r c) =
        (matrixPolynomialEvaluate semicircular P ^ m) r c := congrArg (fun X => X r c) (hp m)
  simp only [closedMatrixAnalyticDerivativeTerm, matrixAnalyticDerivativeTerm,
    matrixExponentialTensorContraction]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro t ht
  rw [closedSandwichPolynomialExpectation_eq]
  change sandwichPolynomialExpectation
    ((closedSemicircularAlgebra I).subtype.toAlgHom
      ((matrixPolynomialEvaluate closedSemicircular P ^ k.val) r s))
    ((closedSemicircularAlgebra I).subtype.toAlgHom
      ((matrixPolynomialEvaluate closedSemicircular P ^ (n - k.val)) t c)) _ = _
  rw [he, he]

/-- Absolute convergence of the actual intrinsic amplified tensor derivative cuts. -/
theorem summable_norm_closedMatrixAnalyticDerivative
    (i : I) (P : Matrix N N (WordPolynomial ℂ I)) (r c : N) (a : ℕ → ℂ)
    (hd : Summable (fun n : ℕ => (n + 1 : ℝ) * ‖a (n + 1)‖ *
      ‖matrixPolynomialEvaluate closedSemicircular P‖ ^ n)) :
    Summable (fun n => ‖a (n + 1) * closedMatrixAnalyticDerivativeTerm i P r c n‖) := by
  have hd' : Summable (fun n : ℕ => (n + 1 : ℝ) * ‖a (n + 1)‖ *
      ‖matrixPolynomialEvaluate semicircular P‖ ^ n) := by
    simpa only [norm_matrixEvaluate_closedSemicircular] using hd
  simpa only [closedMatrixAnalyticDerivativeTerm_eq] using
    summable_norm_matrixAnalyticDerivative i P r c a hd'

/-- Genuine full-matrix analytic-series IBP with intrinsic norm bounds and the actual amplified state. -/
theorem closedGeneratedVacuumState_matrixPolynomial_analyticSeries_integrationByParts
    (i : I) (P : Matrix N N (WordPolynomial ℂ I)) (a : ℕ → ℂ) (r c : N)
    (hv : Summable (fun n => ‖a n‖ * ‖matrixPolynomialEvaluate closedSemicircular P‖ ^ n))
    (hd : Summable (fun n : ℕ => (n + 1 : ℝ) * ‖a (n + 1)‖ *
      ‖matrixPolynomialEvaluate closedSemicircular P‖ ^ n)) :
    matrixExpectation (closedGeneratedVacuumState I).toProbabilitySpace
      (Matrix.diagonal (fun _ : N => closedSemicircular i) *
        analyticSeries a (matrixPolynomialEvaluate closedSemicircular P)) r c =
      ∑' n, a (n + 1) * closedMatrixAnalyticDerivativeTerm i P r c n := by
  simp only [matrixExpectation_apply, Matrix.diagonal_mul]
  change vacuumExpectation ((closedSemicircularAlgebra I).subtype.toAlgHom
    (closedSemicircular i * (analyticSeries a (matrixPolynomialEvaluate closedSemicircular P)) r c)) = _
  rw [map_mul, analyticClosedMatrixInclusion_series_entry P a hv r c]
  simp_rw [closedMatrixAnalyticDerivativeTerm_eq]
  have hv' : Summable (fun n => ‖a n‖ * ‖matrixPolynomialEvaluate semicircular P‖ ^ n) := by
    simpa only [norm_matrixEvaluate_closedSemicircular] using hv
  have hd' : Summable (fun n : ℕ => (n + 1 : ℝ) * ‖a (n + 1)‖ *
      ‖matrixPolynomialEvaluate semicircular P‖ ^ n) := by
    simpa only [norm_matrixEvaluate_closedSemicircular] using hd
  change vacuumExpectation (semicircular i *
    (analyticSeries a (matrixPolynomialEvaluate semicircular P)) r c) = _
  simpa only [Matrix.map_apply, Matrix.diagonal_mul] using
    vacuumState_matrixPolynomial_analyticSeries_integrationByParts i P a r c hv' hd'

end FreeProbability.Fock

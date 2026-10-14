import FreeProbability.RandomMatrix.OrthogonalMultiTraceProducts

/-! # Actual two-trace expectations and second moments -/

noncomputable section
open scoped Classical
namespace FreeProbability.Orthogonal
open Matrix MeasureTheory Filter
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The same Haar matrix is used in both factors of this integral. -/
def twoTraceWordMoment {r s : ℕ} (A B : Fin r → Matrix n n ℂ)
    (C D : Fin s → Matrix n n ℂ) : ℂ :=
  ∫ U : Group n, traceWord A B U * traceWord C D U ∂haar n

/-- An actual two-trace integral is the previously constructed genuine
multi-trace moment. -/
theorem twoTraceWordMoment_eq_multiTrace {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (A B : Fin r → Matrix n n ℂ) (C D : Fin s → Matrix n n ℂ) :
    twoTraceWordMoment A B C D =
      multiTraceWordMoment (twoTracePermutation r s) (twoTraceMatrices A C) (twoTraceMatrices B D) := by
  unfold twoTraceWordMoment multiTraceWordMoment
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun U => (multiTraceWord_twoTrace hr hs A B C D U).symm)

/-- Genuine integrability of two traces of the same random orthogonal matrix. -/
theorem integrable_twoTraceWord {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (A B : Fin r → Matrix n n ℂ) (C D : Fin s → Matrix n n ℂ) :
    Integrable (fun U : Group n => traceWord A B U * traceWord C D U) (haar n) := by
  convert integrable_multiTraceWord (twoTracePermutation r s)
    (twoTraceMatrices A C) (twoTraceMatrices B D) using 1
  funext U
  exact (multiTraceWord_twoTrace hr hs A B C D U).symm

/-- All centered same-Haar two-word expectations have a genuine eventual
uniform quadratic dimension decay, with a threshold depending only on degrees. -/
theorem eventually_centered_twoTraceWordMoment_uniform_bound {r s : ℕ}
    (hr : 0 < r) (hs : 0 < s) (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ N : ℕ in atTop, ∀ (A B : Fin r → Matrix (Fin N) (Fin N) ℂ)
      (C D : Fin s → Matrix (Fin N) (Fin N) ℂ),
      (∀ k, Matrix.trace (A k) = 0) → (∀ k, Matrix.trace (B k) = 0) →
      (∀ k, Matrix.trace (C k) = 0) → (∀ k, Matrix.trace (D k) = 0) →
      (∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A k)‖ ≤ K) →
      (∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B k)‖ ≤ K) →
      (∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (C k)‖ ≤ K) →
      (∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (D k)‖ ≤ K) →
      ‖twoTraceWordMoment A B C D‖ ≤
        orthogonalCenteredTraceConstant (r + s) * K ^ (2 * (r + s)) * ((N : ℝ)⁻¹) ^ 2 := by
  filter_upwards [eventually_centered_multiTraceWordMoment_uniform_bound (r + s) K hK] with N hN
  intro A B C D hA hB hC hD hnA hnB hnC hnD
  have hcAC : ∀ k, Matrix.trace (twoTraceMatrices A C k) = 0 := by
    intro k
    cases h : finSumFinEquiv.symm k <;> simp [twoTraceMatrices, h, hA, hC]
  have hcBD : ∀ k, Matrix.trace (twoTraceMatrices B D k) = 0 := by
    intro k
    cases h : finSumFinEquiv.symm k <;> simp [twoTraceMatrices, h, hB, hD]
  have hnAC : ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (twoTraceMatrices A C k)‖ ≤ K := by
    intro k
    cases h : finSumFinEquiv.symm k <;> simp [twoTraceMatrices, h, hnA, hnC]
  have hnBD : ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (twoTraceMatrices B D k)‖ ≤ K := by
    intro k
    cases h : finSumFinEquiv.symm k <;> simp [twoTraceMatrices, h, hnB, hnD]
  rw [twoTraceWordMoment_eq_multiTrace hr hs]
  simpa only [twoTracePermutation_orbit_card hr hs] using
    hN (twoTracePermutation r s) (twoTraceMatrices A C) (twoTraceMatrices B D) hcAC hcBD hnAC hnBD

/-- Entrywise complex conjugation preserves matrix multiplication. -/
def entrywiseConjugateMatrix (M : Matrix n n ℂ) : Matrix n n ℂ :=
  (starRingEnd ℂ).mapMatrix M

/-- This is entrywise conjugation, not reversal of an ordered matrix word. -/
theorem entrywiseConjugateMatrix_eq (M : Matrix n n ℂ) :
    entrywiseConjugateMatrix M = M.conjTranspose.transpose := by
  ext i j
  rfl

/-- Entrywise conjugation preserves the genuine Euclidean operator norm. -/
theorem entrywiseConjugateMatrix_opNorm (M : Matrix n n ℂ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (entrywiseConjugateMatrix M)‖ =
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) M‖ := by
  rw [entrywiseConjugateMatrix_eq, Euclidean_opNorm_transpose]
  simpa only [Matrix.cstar_norm_def] using Matrix.l2_opNorm_conjTranspose M

/-- Actual matrix traces conjugate entrywise. -/
theorem entrywiseConjugateMatrix_trace (M : Matrix n n ℂ) :
    Matrix.trace (entrywiseConjugateMatrix M) = (starRingEnd ℂ) (Matrix.trace M) :=
  (AddMonoidHom.map_trace (starRingEnd ℂ) M).symm

/-- The actual real orthogonal matrix complexification is fixed by entrywise conjugation. -/
theorem entrywiseConjugateMatrix_complexMatrix (U : Group n) :
    entrywiseConjugateMatrix (complexMatrix U) = complexMatrix U := by
  ext i j
  simp [entrywiseConjugateMatrix, RingHom.mapMatrix_apply, complexMatrix]

/-- Conjugating an actual trace observable keeps both deterministic words in
order, because the random orthogonal entries are real. -/
theorem traceWord_conjugate {r : ℕ} (A B : Fin r → Matrix n n ℂ) (U : Group n) :
    (starRingEnd ℂ) (traceWord A B U) =
      traceWord (fun k => entrywiseConjugateMatrix (A k))
        (fun k => entrywiseConjugateMatrix (B k)) U := by
  have ht : entrywiseConjugateMatrix (complexMatrix U).transpose = (complexMatrix U).transpose := by
    rw [entrywiseConjugateMatrix_eq]
    ext i j
    simp [Matrix.conjTranspose_apply, complexMatrix]
  have hb (k : Fin r) : entrywiseConjugateMatrix
      (complexMatrix U * A k * (complexMatrix U).transpose * B k) =
      complexMatrix U * entrywiseConjugateMatrix (A k) * (complexMatrix U).transpose *
        entrywiseConjugateMatrix (B k) := by
    unfold entrywiseConjugateMatrix
    rw [map_mul, map_mul, map_mul]
    change entrywiseConjugateMatrix (complexMatrix U) * entrywiseConjugateMatrix (A k) *
      entrywiseConjugateMatrix (complexMatrix U).transpose * entrywiseConjugateMatrix (B k) = _
    rw [entrywiseConjugateMatrix_complexMatrix, ht]
    rfl
  have hp : entrywiseConjugateMatrix (List.ofFn (fun k =>
      complexMatrix U * A k * (complexMatrix U).transpose * B k)).prod =
      (List.ofFn (fun k => complexMatrix U * entrywiseConjugateMatrix (A k) *
        (complexMatrix U).transpose * entrywiseConjugateMatrix (B k))).prod := by
    unfold entrywiseConjugateMatrix
    rw [map_list_prod, List.map_ofFn]
    exact congrArg (fun f : Fin r → Matrix n n ℂ => (List.ofFn f).prod) (funext hb)
  change (starRingEnd ℂ) ((Fintype.card n : ℂ)⁻¹ * Matrix.trace _) = _
  rw [map_mul, map_inv₀, map_natCast, ← entrywiseConjugateMatrix_trace, hp]
  rfl

/-- The actual second absolute moment, without an independence premise. -/
def traceWordSecondMoment {r : ℕ} (A B : Fin r → Matrix n n ℂ) : ℝ :=
  ∫ U : Group n, ‖traceWord A B U‖ ^ 2 ∂haar n

/-- The actual squared-norm integral is the actual same-Haar conjugate product integral. -/
theorem traceWordSecondMoment_eq_twoTrace {r : ℕ} (A B : Fin r → Matrix n n ℂ) :
    (traceWordSecondMoment A B : ℂ) =
      twoTraceWordMoment A B (fun k => entrywiseConjugateMatrix (A k))
        (fun k => entrywiseConjugateMatrix (B k)) := by
  rw [traceWordSecondMoment, ← integral_complex_ofReal]
  unfold twoTraceWordMoment
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun U => by
    dsimp only
    rw [← traceWord_conjugate, Complex.mul_conj, Complex.normSq_eq_norm_sq])

/-- The actual second absolute moment is nonnegative. -/
theorem traceWordSecondMoment_nonneg {r : ℕ} (A B : Fin r → Matrix n n ℂ) :
    0 ≤ traceWordSecondMoment A B :=
  integral_nonneg (fun _ => sq_nonneg _)

/-- Actual centered trace words have a genuine eventual uniform second
absolute moment bound of order dimension to the power minus two. -/
theorem eventually_centered_traceWordSecondMoment_bound {r : ℕ}
    (hr : 0 < r) (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ N : ℕ in atTop, ∀ (A B : Fin r → Matrix (Fin N) (Fin N) ℂ),
      (∀ k, Matrix.trace (A k) = 0) → (∀ k, Matrix.trace (B k) = 0) →
      (∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A k)‖ ≤ K) →
      (∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B k)‖ ≤ K) →
      traceWordSecondMoment A B ≤
        orthogonalCenteredTraceConstant (r + r) * K ^ (2 * (r + r)) * ((N : ℝ)⁻¹) ^ 2 := by
  filter_upwards [eventually_centered_twoTraceWordMoment_uniform_bound hr hr K hK] with N hN
  intro A B hA hB hnA hnB
  have hcA : ∀ k, Matrix.trace (entrywiseConjugateMatrix (A k)) = 0 := by
    intro k
    rw [entrywiseConjugateMatrix_trace, hA k, map_zero]
  have hcB : ∀ k, Matrix.trace (entrywiseConjugateMatrix (B k)) = 0 := by
    intro k
    rw [entrywiseConjugateMatrix_trace, hB k, map_zero]
  have hnAc : ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (entrywiseConjugateMatrix (A k))‖ ≤ K := by
    intro k
    rw [entrywiseConjugateMatrix_opNorm]
    exact hnA k
  have hnBc : ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (entrywiseConjugateMatrix (B k))‖ ≤ K := by
    intro k
    rw [entrywiseConjugateMatrix_opNorm]
    exact hnB k
  have he := hN A B (fun k => entrywiseConjugateMatrix (A k))
    (fun k => entrywiseConjugateMatrix (B k)) hA hB hcA hcB hnA hnB hnAc hnBc
  rw [← traceWordSecondMoment_eq_twoTrace] at he
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (traceWordSecondMoment_nonneg A B)] using he

end FreeProbability.Orthogonal

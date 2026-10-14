import FreeProbability.RandomMatrix.OrthogonalWeingarten
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Actual orthogonal Haar trace words and deterministic contractions -/

noncomputable section
open scoped Classical
namespace FreeProbability.Orthogonal
open Matrix MeasureTheory
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Normalization is zero in dimension zero, including the empty word. -/
def normalizedTrace (C : Matrix n n ℂ) : ℂ := (Fintype.card n : ℂ)⁻¹ * Matrix.trace C

/-- Complexification of an actual real orthogonal matrix. -/
def complexMatrix (U : Group n) : Matrix n n ℂ := fun a b => (U a b : ℂ)

theorem complexMatrix_conjTranspose (U : Group n) :
    (complexMatrix U).conjTranspose = (complexMatrix U).transpose := by
  ext a b
  simp [complexMatrix, Matrix.conjTranspose_apply, Matrix.transpose_apply]

/-- Ordered cyclic conjugation word with complex deterministic factors. -/
def traceWord {r : ℕ} (A B : Fin r → Matrix n n ℂ) (U : Group n) : ℂ :=
  normalizedTrace (List.ofFn (fun k => complexMatrix U * A k * (complexMatrix U).transpose * B k)).prod

abbrev TraceCode (n : Type*) := n × n × n × n

def traceCodeFactor (A B : Matrix n n ℂ) (s : TraceCode n) : Matrix n n ℂ :=
  A s.2.1 s.2.2.2 • (Matrix.single s.1 s.2.2.1 (1 : ℂ) * B)

private theorem block_expansion (A B : Matrix n n ℂ) (U : Group n) :
    complexMatrix U * A * (complexMatrix U).transpose * B =
      ∑ s : TraceCode n, ((U s.1 s.2.1 : ℂ) * (U s.2.2.1 s.2.2.2 : ℂ)) • traceCodeFactor A B s := by
  ext x y
  simp only [Matrix.sum_apply, Fintype.sum_prod_type, Matrix.smul_apply, smul_eq_mul,
    traceCodeFactor, Matrix.mul_apply, Matrix.transpose_apply, complexMatrix, Matrix.single]
  simp only [Finset.mul_sum, Finset.sum_mul]
  simp only [ite_and]
  simp [mul_assoc, mul_left_comm, mul_comm]
  conv_lhs => arg 2; intro c; rw [Finset.sum_comm]
  exact Finset.sum_comm

private theorem ordered_product_sum {C R : Type*} [Fintype C] [Semiring R]
    (r : ℕ) (f : Fin r → C → R) :
    (List.ofFn (fun k => ∑ c, f k c)).prod =
      ∑ s : Fin r → C, (List.ofFn (fun k => f k (s k))).prod := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [List.ofFn_succ, List.prod_cons, ih]
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (r + 1) => C))]
    simp only [Fintype.sum_prod_type, Fin.consEquiv_apply, List.ofFn_succ, List.prod_cons,
      Fin.cons_zero, Fin.cons_succ, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm

/-- The sites first list the U entries and then the transposed-U entries. -/
def traceSites (r : ℕ) : Fin (2 * r) ≃ Fin r ⊕ Fin r :=
  (finCongr (by omega)).trans finSumFinEquiv.symm

def traceRows {r : ℕ} (s : Fin r → TraceCode n) : Fin (2 * r) → n :=
  fun a => Sum.elim (fun k => (s k).1) (fun k => (s k).2.2.1) (traceSites r a)

def traceCols {r : ℕ} (s : Fin r → TraceCode n) : Fin (2 * r) → n :=
  fun a => Sum.elim (fun k => (s k).2.1) (fun k => (s k).2.2.2) (traceSites r a)

def traceContractionCoefficient {r : ℕ} (A B : Fin r → Matrix n n ℂ)
    (s : Fin r → TraceCode n) : ℂ :=
  normalizedTrace (List.ofFn (fun k => traceCodeFactor (A k) (B k) (s k))).prod

private theorem code_scalar_product {r : ℕ} (s : Fin r → TraceCode n) (U : Group n) :
    (∏ k, (U (s k).1 (s k).2.1 : ℂ) * (U (s k).2.2.1 (s k).2.2.2 : ℂ)) =
      (entryMonomial (traceRows s) (traceCols s) U : ℂ) := by
  rw [entryMonomial, Complex.ofReal_prod]
  rw [← Equiv.prod_comp (traceSites r).symm]
  simp only [traceRows, traceCols, Equiv.apply_symm_apply, Fintype.prod_sum_type,
    Sum.elim_inl, Sum.elim_inr, Finset.prod_mul_distrib]

private theorem ordered_product_smul {r : ℕ} (c : Fin r → ℂ)
    (D : Fin r → Matrix n n ℂ) :
    (List.ofFn (fun k => c k • D k)).prod = (∏ k, c k) • (List.ofFn D).prod := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [List.ofFn_succ, List.prod_cons, ih, List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

/-- Exact expansion of the actual cyclic trace word into genuine entry
monomials with explicit deterministic matrix-unit contractions. -/
theorem traceWord_eq_entryMonomial_sum {r : ℕ} (A B : Fin r → Matrix n n ℂ)
    (U : Group n) :
    traceWord A B U = ∑ s : Fin r → TraceCode n,
      traceContractionCoefficient A B s * (entryMonomial (traceRows s) (traceCols s) U : ℂ) := by
  unfold traceWord
  simp_rw [block_expansion]
  rw [ordered_product_sum]
  simp_rw [ordered_product_smul, code_scalar_product]
  unfold normalizedTrace traceContractionCoefficient
  rw [Matrix.trace_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [Matrix.trace_smul]
  simp only [smul_eq_mul, normalizedTrace]
  ring

/-- The actual Haar integral of the cyclic word. -/
def traceWordMoment {r : ℕ} (A B : Fin r → Matrix n n ℂ) : ℂ :=
  ∫ U, traceWord A B U ∂haar n

private theorem integrable_code_term {r : ℕ} (A B : Fin r → Matrix n n ℂ)
    (s : Fin r → TraceCode n) :
    Integrable (fun U : Group n => traceContractionCoefficient A B s *
      (entryMonomial (traceRows s) (traceCols s) U : ℂ)) (haar n) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact continuous_const.mul (Complex.continuous_ofReal.comp (continuous_entryMonomial _ _))
  · exact HasCompactSupport.of_compactSpace _

/-- Integration of the exact expansion yields the genuine Haar entry moments. -/
theorem traceWordMoment_eq_entryMoment_sum {r : ℕ} (A B : Fin r → Matrix n n ℂ) :
    traceWordMoment A B = ∑ s : Fin r → TraceCode n,
      traceContractionCoefficient A B s * (entryMoment (traceRows s) (traceCols s) : ℂ) := by
  unfold traceWordMoment
  simp_rw [traceWord_eq_entryMonomial_sum]
  rw [integral_finsetSum _ (fun s _ => integrable_code_term A B s)]
  simp_rw [integral_const_mul, integral_complex_ofReal, entryMoment]

theorem integrable_traceWord {r : ℕ} (A B : Fin r → Matrix n n ℂ) :
    Integrable (traceWord A B) (haar n) := by
  have h : Integrable (fun U : Group n => ∑ s : Fin r → TraceCode n,
      traceContractionCoefficient A B s * (entryMonomial (traceRows s) (traceCols s) U : ℂ))
      (haar n) := integrable_finsetSum _ (fun s _ => integrable_code_term A B s)
  exact h.congr (Filter.Eventually.of_forall (fun U => (traceWord_eq_entryMonomial_sum A B U).symm))

/-- An explicit deterministic contraction, with no cycle-count interpretation
or operator-norm estimate supplied as a premise. -/
def tracePairingContraction {r : ℕ} (A B : Fin r → Matrix n n ℂ)
    (p q : OrdinaryPairing r) : ℂ :=
  ∑ s : Fin r → TraceCode n, traceContractionCoefficient A B s *
    (ordinaryPairingDelta p (traceRows s) : ℂ) * (ordinaryPairingDelta q (traceCols s) : ℂ)

/-- The stable actual cyclic normalized Haar trace is the genuine inverse-Gram
pairing-contraction sum, for arbitrary complex deterministic matrices. -/
theorem traceWordMoment_eq_weingarten_contractions {r : ℕ} (hr : r ≤ Fintype.card n)
    (A B : Fin r → Matrix n n ℂ) :
    traceWordMoment A B = ∑ p : OrdinaryPairing r, ∑ q : OrdinaryPairing r,
      ((ordinaryPairingGram n r)⁻¹ p q : ℂ) * tracePairingContraction A B p q := by
  rw [traceWordMoment_eq_entryMoment_sum]
  simp_rw [entryMoment_eq_weingarten_delta_sum hr, Complex.ofReal_sum, Complex.ofReal_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  unfold tracePairingContraction
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- The empty-word convention is exactly normalized trace of the identity. -/
theorem traceWordMoment_zero (A B : Fin 0 → Matrix n n ℂ) :
    traceWordMoment A B = (Fintype.card n : ℂ)⁻¹ * (Fintype.card n : ℂ) := by
  simp [traceWordMoment, traceWord, normalizedTrace, Matrix.trace_one]

theorem traceWordMoment_zero_of_card_pos (hn : 0 < Fintype.card n)
    (A B : Fin 0 → Matrix n n ℂ) : traceWordMoment A B = 1 := by
  rw [traceWordMoment_zero]
  exact inv_mul_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hn))

/-- In empty dimension normalized trace words are zero at every degree. -/
theorem traceWordMoment_of_card_zero {r : ℕ} (hn : Fintype.card n = 0)
    (A B : Fin r → Matrix n n ℂ) : traceWordMoment A B = 0 := by
  simp [traceWordMoment, traceWord, normalizedTrace, hn]

end FreeProbability.Orthogonal

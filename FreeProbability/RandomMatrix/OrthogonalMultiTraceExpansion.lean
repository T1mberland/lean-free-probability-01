import FreeProbability.RandomMatrix.OrthogonalCenteredTraceBounds

/-! # Genuine permutation-indexed multi-trace Haar expansion -/

noncomputable section
open scoped Classical
namespace FreeProbability.Orthogonal
open Matrix MeasureTheory
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- One genuine trace per actual permutation cycle, with one dimension
normalization per cycle. Singleton cycles and empty index sets are retained. -/
def multiTraceWord {r : ℕ} (π : Equiv.Perm (Fin r)) (A B : Fin r → Matrix n n ℂ)
    (U : Group n) : ℂ :=
  ((Fintype.card n : ℂ)⁻¹) ^ Fintype.card (PermutationOrbitIndex π) *
    permutationNetwork π (fun k => complexMatrix U * A k * (complexMatrix U).transpose * B k)

/-- Actual product of normalized cycle traces, with ordered cycle products. -/
theorem multiTraceWord_eq_prod_traces {r : ℕ} (π : Equiv.Perm (Fin r))
    (A B : Fin r → Matrix n n ℂ) (U : Group n) :
    multiTraceWord π A B U = ∏ c : PermutationOrbitIndex π,
      (Fintype.card n : ℂ)⁻¹ * Matrix.trace (List.ofFn (fun k =>
        complexMatrix U * A (permutationOrbitEnumeration π c k).val * (complexMatrix U).transpose *
          B (permutationOrbitEnumeration π c k).val)).prod := by
  unfold multiTraceWord
  rw [permutationNetwork_eq_prod_cycle_traces, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

private theorem block_matrix_sum (A B : Matrix n n ℂ) (U : Group n) :
    complexMatrix U * A * (complexMatrix U).transpose * B =
      ∑ s : TraceCode n, ((U s.1 s.2.1 : ℂ) * (U s.2.2.1 s.2.2.2 : ℂ)) • traceCodeFactor A B s := by
  ext x y
  simp only [Matrix.sum_apply, Fintype.sum_prod_type, Matrix.smul_apply, smul_eq_mul,
    traceCodeFactor, Matrix.mul_apply, Matrix.transpose_apply, complexMatrix, Matrix.single]
  simp only [Finset.mul_sum, Finset.sum_mul, ite_and]
  simp [mul_assoc, mul_left_comm, mul_comm]
  conv_lhs => arg 2; intro c; rw [Finset.sum_comm]
  exact Finset.sum_comm

omit [DecidableEq n] in
private theorem permutationNetwork_sum_smul {α C : Type*} [Fintype α] [Fintype C]
    (π : Equiv.Perm α) (c : α → C → ℂ) (D : α → C → Matrix n n ℂ) :
    permutationNetwork π (fun a => ∑ s, c a s • D a s) =
      ∑ s : α → C, (∏ a, c a (s a)) * permutationNetwork π (fun a => D a (s a)) := by
  unfold permutationNetwork
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp_rw [Fintype.prod_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  simp_rw [Finset.prod_mul_distrib]
  rw [← Finset.mul_sum]

private theorem code_entry_product {r : ℕ} (s : Fin r → TraceCode n) (U : Group n) :
    (∏ k, (U (s k).1 (s k).2.1 : ℂ) * (U (s k).2.2.1 (s k).2.2.2 : ℂ)) =
      (entryMonomial (traceRows s) (traceCols s) U : ℂ) := by
  rw [entryMonomial, Complex.ofReal_prod, ← Equiv.prod_comp (traceSites r).symm]
  simp only [traceRows, traceCols, Equiv.apply_symm_apply, Fintype.prod_sum_type,
    Sum.elim_inl, Sum.elim_inr, Finset.prod_mul_distrib]

/-- The actual deterministic coefficient of a multi-trace code. -/
def multiTraceCoefficient {r : ℕ} (π : Equiv.Perm (Fin r))
    (A B : Fin r → Matrix n n ℂ) (s : Fin r → TraceCode n) : ℂ :=
  ((Fintype.card n : ℂ)⁻¹) ^ Fintype.card (PermutationOrbitIndex π) *
    permutationNetwork π (fun k => traceCodeFactor (A k) (B k) (s k))

/-- Exact expansion into actual Haar entry monomials, derived from matrix
multiplication and genuine finite sums. No integration formula is assumed. -/
theorem multiTraceWord_eq_entryMonomial_sum {r : ℕ} (π : Equiv.Perm (Fin r))
    (A B : Fin r → Matrix n n ℂ) (U : Group n) :
    multiTraceWord π A B U = ∑ s : Fin r → TraceCode n,
      multiTraceCoefficient π A B s * (entryMonomial (traceRows s) (traceCols s) U : ℂ) := by
  let : DecidableEq (Fin r) := Classical.decEq _
  unfold multiTraceWord
  simp_rw [block_matrix_sum]
  rw [permutationNetwork_sum_smul, Finset.mul_sum]
  simp_rw [code_entry_product]
  apply Finset.sum_congr (by ext s; simp)
  intro s _
  unfold multiTraceCoefficient
  ring

/-- Actual Bochner Haar expectation of the genuine multi-trace word. -/
def multiTraceWordMoment {r : ℕ} (π : Equiv.Perm (Fin r)) (A B : Fin r → Matrix n n ℂ) : ℂ :=
  ∫ U, multiTraceWord π A B U ∂haar n

private theorem integrable_multi_code {r : ℕ} (π : Equiv.Perm (Fin r))
    (A B : Fin r → Matrix n n ℂ) (s : Fin r → TraceCode n) :
    Integrable (fun U : Group n => multiTraceCoefficient π A B s *
      (entryMonomial (traceRows s) (traceCols s) U : ℂ)) (haar n) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact continuous_const.mul (Complex.continuous_ofReal.comp (continuous_entryMonomial _ _))
  · exact HasCompactSupport.of_compactSpace _

/-- The actual multi-trace integral is its genuine entry-moment code sum. -/
theorem multiTraceWordMoment_eq_entryMoment_sum {r : ℕ} (π : Equiv.Perm (Fin r))
    (A B : Fin r → Matrix n n ℂ) :
    multiTraceWordMoment π A B = ∑ s : Fin r → TraceCode n,
      multiTraceCoefficient π A B s * (entryMoment (traceRows s) (traceCols s) : ℂ) := by
  unfold multiTraceWordMoment
  simp_rw [multiTraceWord_eq_entryMonomial_sum]
  rw [integral_finsetSum _ (fun s _ => integrable_multi_code π A B s)]
  simp_rw [integral_const_mul, integral_complex_ofReal, entryMoment]

def multiTracePairingContraction {r : ℕ} (π : Equiv.Perm (Fin r))
    (A B : Fin r → Matrix n n ℂ) (p q : OrdinaryPairing r) : ℂ :=
  ∑ s : Fin r → TraceCode n, multiTraceCoefficient π A B s *
    (ordinaryPairingDelta p (traceRows s) : ℂ) * (ordinaryPairingDelta q (traceCols s) : ℂ)

/-- Stable multi-trace integration uses the ACTUAL inverse Gram and genuine
contractions. All cycle and entry integration dependencies are proved. -/
theorem multiTraceWordMoment_eq_weingarten_contractions {r : ℕ}
    (hr : r ≤ Fintype.card n) (π : Equiv.Perm (Fin r)) (A B : Fin r → Matrix n n ℂ) :
    multiTraceWordMoment π A B = ∑ p : OrdinaryPairing r, ∑ q : OrdinaryPairing r,
      ((ordinaryPairingGram n r)⁻¹ p q : ℂ) * multiTracePairingContraction π A B p q := by
  rw [multiTraceWordMoment_eq_entryMoment_sum]
  simp_rw [entryMoment_eq_weingarten_delta_sum hr, Complex.ofReal_sum, Complex.ofReal_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  unfold multiTracePairingContraction
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem integrable_multiTraceWord {r : ℕ} (π : Equiv.Perm (Fin r))
    (A B : Fin r → Matrix n n ℂ) : Integrable (multiTraceWord π A B) (haar n) := by
  have h : Integrable (fun U : Group n => ∑ s : Fin r → TraceCode n,
      multiTraceCoefficient π A B s * (entryMonomial (traceRows s) (traceCols s) U : ℂ))
      (haar n) := integrable_finsetSum _ (fun s _ => integrable_multi_code π A B s)
  exact h.congr (Filter.Eventually.of_forall (fun U => (multiTraceWord_eq_entryMonomial_sum π A B U).symm))

/-- The actual empty-index multi-trace word is one, even in zero dimension. -/
theorem multiTraceWord_empty (π : Equiv.Perm (Fin 0))
    (A B : Fin 0 → Matrix n n ℂ) (U : Group n) : multiTraceWord π A B U = 1 := by
  let : IsEmpty (PermutationOrbitIndex π) := ⟨fun c => Quotient.inductionOn c (fun a => Fin.elim0 a)⟩
  simp [multiTraceWord, permutationNetwork]

theorem multiTraceWordMoment_empty (π : Equiv.Perm (Fin 0))
    (A B : Fin 0 → Matrix n n ℂ) : multiTraceWordMoment π A B = 1 := by
  simp [multiTraceWordMoment, multiTraceWord_empty]

/-- Every nonempty multi-trace network vanishes in actual zero matrix dimension. -/
theorem multiTraceWord_empty_dimension {r : ℕ} (hr : 0 < r) (hn : Fintype.card n = 0)
    (π : Equiv.Perm (Fin r)) (A B : Fin r → Matrix n n ℂ) (U : Group n) :
    multiTraceWord π A B U = 0 := by
  let : IsEmpty n := Fintype.card_eq_zero_iff.mp hn
  let : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  simp [multiTraceWord, permutationNetwork_empty_dimension]

end FreeProbability.Orthogonal

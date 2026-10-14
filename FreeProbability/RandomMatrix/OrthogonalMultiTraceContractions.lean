import FreeProbability.RandomMatrix.OrthogonalMultiTraceExpansion

/-! # Genuine multi-trace matrix-unit evaluation and paired network factors -/

noncomputable section
open scoped Classical
namespace FreeProbability.Orthogonal
open Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] in
private theorem tuple_indicator {r : ℕ} (u a : Fin r → n) :
    (∏ k, if u k = a k then (1 : ℂ) else 0) = if u = a then 1 else 0 := by
  by_cases h : u = a
  · subst a
    simp
  · simp only [h, ite_false]
    obtain ⟨k, hk⟩ : ∃ k, u k ≠ a k := by
      by_contra hn
      push Not at hn
      exact h (funext hn)
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp only [hk, ite_false])

private theorem code_factor_entry (A B : Matrix n n ℂ) (s : TraceCode n) (x y : n) :
    traceCodeFactor A B s x y = A s.2.1 s.2.2.2 * (if x = s.1 then B s.2.2.1 y else 0) := by
  simp [traceCodeFactor, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.single,
    ite_and, eq_comm]

/-- Genuine permutation-indexed code evaluation, valid even at degree zero.
Each matrix unit forces its own actual row coloring. -/
theorem multiTraceCoefficient_eq_entries {r : ℕ} (π : Equiv.Perm (Fin r))
    (A B : Fin r → Matrix n n ℂ) (s : Fin r → TraceCode n) :
    multiTraceCoefficient π A B s =
      ((Fintype.card n : ℂ)⁻¹) ^ Fintype.card (PermutationOrbitIndex π) *
        (∏ k, A k (s k).2.1 (s k).2.2.2) * (∏ k, B k (s k).2.2.1 (s (π k)).1) := by
  unfold multiTraceCoefficient permutationNetwork
  have he (u : Fin r → n) (k : Fin r) :
      traceCodeFactor (A k) (B k) (s k) (u k) (u (π k)) =
      A k (s k).2.1 (s k).2.2.2 * B k (s k).2.2.1 (u (π k)) *
        (if u k = (s k).1 then 1 else 0) := by
    rw [code_factor_entry]
    split <;> simp_all
  simp_rw [he, Finset.prod_mul_distrib, tuple_indicator, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true, mul_assoc]

/-- The literal deterministic row-edge pairing for any actual trace permutation. -/
def multiTraceRowEdgeCode {r : ℕ} (π : Equiv.Perm (Fin r)) : PairingSites r where
  toFun a := (traceSites r a).elim (fun k => (π.symm k, 1)) (fun k => (k, 0))
  invFun z := if z.2 = 0 then (traceSites r).symm (.inr z.1) else (traceSites r).symm (.inl (π z.1))
  left_inv a := by
    obtain ⟨a, rfl⟩ := (traceSites r).symm.surjective a
    cases a <;> simp
  right_inv z := by
    rcases z with ⟨k, b⟩
    fin_cases b <;> simp

theorem multiTraceRowEdgeCode_symm_zero {r : ℕ} (π : Equiv.Perm (Fin r)) (k : Fin r) :
    (multiTraceRowEdgeCode π).symm (k, 0) = (traceSites r).symm (.inr k) := by
  simp [multiTraceRowEdgeCode]

theorem multiTraceRowEdgeCode_symm_one {r : ℕ} (π : Equiv.Perm (Fin r)) (k : Fin r) :
    (multiTraceRowEdgeCode π).symm (k, 1) = (traceSites r).symm (.inl (π k)) := by
  simp [multiTraceRowEdgeCode]

/-- The actual paired row network associated with all genuine trace cycles. -/
def multiTraceRowNetwork {r : ℕ} (π : Equiv.Perm (Fin r))
    (B : Fin r → Matrix n n ℂ) (p : OrdinaryPairing r) : ℂ :=
  ∑ i : Fin (2 * r) → n,
    (∏ k, B k (i ((traceSites r).symm (.inr k)))
      (i ((traceSites r).symm (.inl (π k))))) * (ordinaryPairingDelta p i : ℂ)

theorem multiTraceRowNetwork_eq_pairingNetwork {r : ℕ} (π : Equiv.Perm (Fin r))
    (B : Fin r → Matrix n n ℂ) (p : OrdinaryPairing r) :
    multiTraceRowNetwork π B p = pairingNetwork p (multiTraceRowEdgeCode π) B := by
  unfold multiTraceRowNetwork pairingNetwork
  simp only [multiTraceRowEdgeCode_symm_zero, multiTraceRowEdgeCode_symm_one]

omit [Fintype n] [DecidableEq n] in
private theorem code_inverse_rows {r : ℕ} (z : (Fin (2 * r) → n) × (Fin (2 * r) → n)) :
    traceRows ((traceCodeEquiv r).symm z) = z.1 :=
  congrArg Prod.fst ((traceCodeEquiv r).apply_symm_apply z)

omit [Fintype n] [DecidableEq n] in
private theorem code_inverse_cols {r : ℕ} (z : (Fin (2 * r) → n) × (Fin (2 * r) → n)) :
    traceCols ((traceCodeEquiv r).symm z) = z.2 :=
  congrArg Prod.snd ((traceCodeEquiv r).apply_symm_apply z)

omit [Fintype n] [DecidableEq n] in
private theorem code_inverse_apply {r : ℕ} (z : (Fin (2 * r) → n) × (Fin (2 * r) → n)) (k : Fin r) :
    (traceCodeEquiv r).symm z k = (z.1 ((traceSites r).symm (.inl k)),
      z.2 ((traceSites r).symm (.inl k)), z.1 ((traceSites r).symm (.inr k)),
      z.2 ((traceSites r).symm (.inr k))) := rfl

/-- The ACTUAL multi-trace contraction factors into genuine paired row and
column networks, with one normalization per actual trace cycle. -/
theorem multiTracePairingContraction_eq_network_product {r : ℕ} (π : Equiv.Perm (Fin r))
    (A B : Fin r → Matrix n n ℂ) (p q : OrdinaryPairing r) :
    multiTracePairingContraction π A B p q =
      ((Fintype.card n : ℂ)⁻¹) ^ Fintype.card (PermutationOrbitIndex π) *
        multiTraceRowNetwork π B p * traceColumnNetwork A q := by
  unfold multiTracePairingContraction
  rw [← Equiv.sum_comp (traceCodeEquiv (n := n) r).symm]
  simp_rw [multiTraceCoefficient_eq_entries]
  simp only [Fintype.sum_prod_type, code_inverse_rows, code_inverse_cols, code_inverse_apply]
  unfold multiTraceRowNetwork traceColumnNetwork
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The actual multi-trace row network has its genuine raw-loop operator bound. -/
theorem multiTraceRowNetwork_norm_le {r : ℕ} (π : Equiv.Perm (Fin r))
    (B : Fin r → Matrix n n ℂ) (p : OrdinaryPairing r) :
    ‖multiTraceRowNetwork π B p‖ ≤
      (Fintype.card n : ℝ) ^ pairingLoopCount p (Quotient.mk _ (multiTraceRowEdgeCode π)) *
        ∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B k)‖ := by
  rw [multiTraceRowNetwork_eq_pairingNetwork]
  exact pairingNetwork_norm_le _ _ _

end FreeProbability.Orthogonal

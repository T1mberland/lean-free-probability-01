import FreeProbability.RandomMatrix.OrthogonalTraceWordExpansion
import Mathlib.Logic.Equiv.Fin.Rotate

/-! # Exact cyclic entry contractions and row-column factorization -/

noncomputable section
open scoped Classical
namespace FreeProbability.Orthogonal
open Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

private def rowMatrix (a : n) (v : n → ℂ) : Matrix n n ℂ :=
  fun x y => if x = a then v y else 0

private theorem rowMatrix_product_entry (r : ℕ) (a : Fin (r + 1) → n)
    (v : Fin (r + 1) → n → ℂ) (x y : n) :
    (List.ofFn (fun k => rowMatrix (a k) (v k))).prod x y =
      (if x = a 0 then 1 else 0) *
        (∏ k : Fin r, v k.castSucc (a k.succ)) * v (Fin.last r) y := by
  induction r generalizing x y with
  | zero => simp [List.ofFn_succ, rowMatrix]
  | succ r ih =>
    rw [List.ofFn_succ, List.prod_cons, Matrix.mul_apply]
    simp_rw [ih]
    simp only [rowMatrix]
    rw [Fin.prod_univ_succ]
    simp only [Fin.castSucc_zero, Fin.castSucc_succ,
      Fin.succ_last]
    split_ifs <;> simp_all [mul_assoc]
    change (∑ t : n, v 0 t * ((if t = a 1 then (1 : ℂ) else 0) *
      ((∏ k : Fin r, v k.castSucc.succ (a k.succ.succ)) * v (Fin.last (r + 1)) y))) =
      v 0 (a 1) * ((∏ k : Fin r, v k.castSucc.succ (a k.succ.succ)) * v (Fin.last (r + 1)) y)
    simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]

private theorem rowMatrix_word_trace (r : ℕ) (a : Fin (r + 1) → n)
    (v : Fin (r + 1) → n → ℂ) :
    Matrix.trace (List.ofFn (fun k => rowMatrix (a k) (v k))).prod =
      ∏ k : Fin (r + 1), v k (a (finRotate (r + 1) k)) := by
  change (∑ x, (List.ofFn (fun k => rowMatrix (a k) (v k))).prod x x) = _
  simp_rw [rowMatrix_product_entry]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Fin.prod_univ_castSucc, finRotate_last]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  congr 2
  exact (finRotate_of_lt k.isLt).symm

private theorem rowMatrix_eq_single_mul (a c : n) (B : Matrix n n ℂ) :
    rowMatrix a (B c) = Matrix.single a c 1 * B := by
  ext x y
  simp [rowMatrix, Matrix.mul_apply, Matrix.single, ite_and, eq_comm]

private theorem scalar_word_product {r : ℕ} (c : Fin r → ℂ) (D : Fin r → Matrix n n ℂ) :
    (List.ofFn (fun k => c k • D k)).prod = (∏ k, c k) • (List.ofFn D).prod := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [List.ofFn_succ, List.prod_cons, ih, List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

/-- Genuine matrix-unit cyclic trace evaluation, with the actual ordered
matrix product on the left. Positive degree is required for the cycle. -/
theorem traceContractionCoefficient_eq_cyclic_entries {r : ℕ} (hr : 0 < r)
    (A B : Fin r → Matrix n n ℂ) (s : Fin r → TraceCode n) :
    traceContractionCoefficient A B s = (Fintype.card n : ℂ)⁻¹ *
      (∏ k, A k (s k).2.1 (s k).2.2.2) *
      (∏ k, B k (s k).2.2.1 (s (finRotate r k)).1) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  unfold traceContractionCoefficient traceCodeFactor
  rw [scalar_word_product]
  unfold normalizedTrace
  rw [Matrix.trace_smul]
  simp only [smul_eq_mul]
  simp_rw [← rowMatrix_eq_single_mul]
  rw [rowMatrix_word_trace]
  ring

/-- Codes are exactly independently chosen row and column site tuples. -/
def traceCodeEquiv (r : ℕ) : (Fin r → TraceCode n) ≃
    (Fin (2 * r) → n) × (Fin (2 * r) → n) where
  toFun s := (traceRows s, traceCols s)
  invFun z k := (z.1 ((traceSites r).symm (.inl k)),
    z.2 ((traceSites r).symm (.inl k)), z.1 ((traceSites r).symm (.inr k)),
    z.2 ((traceSites r).symm (.inr k)))
  left_inv s := by
    funext k
    simp [traceRows, traceCols]
  right_inv z := by
    apply Prod.ext <;> funext a <;>
      obtain ⟨a, rfl⟩ := (traceSites r).symm.surjective a <;>
      cases a <;> simp [traceRows, traceCols]

omit [Fintype n] [DecidableEq n] in
private theorem traceCodeEquiv_symm_apply (r : ℕ)
    (z : (Fin (2 * r) → n) × (Fin (2 * r) → n)) (k : Fin r) :
    (traceCodeEquiv r).symm z k = (z.1 ((traceSites r).symm (.inl k)),
      z.2 ((traceSites r).symm (.inl k)), z.1 ((traceSites r).symm (.inr k)),
      z.2 ((traceSites r).symm (.inr k))) := rfl

omit [Fintype n] [DecidableEq n] in
private theorem traceRows_symm (r : ℕ)
    (z : (Fin (2 * r) → n) × (Fin (2 * r) → n)) :
    traceRows ((traceCodeEquiv r).symm z) = z.1 :=
  congrArg Prod.fst ((traceCodeEquiv r).apply_symm_apply z)

omit [Fintype n] [DecidableEq n] in
private theorem traceCols_symm (r : ℕ)
    (z : (Fin (2 * r) → n) × (Fin (2 * r) → n)) :
    traceCols ((traceCodeEquiv r).symm z) = z.2 :=
  congrArg Prod.snd ((traceCodeEquiv r).apply_symm_apply z)

/-- The genuine row network with paired labels. -/
def traceRowNetwork {r : ℕ} (B : Fin r → Matrix n n ℂ) (p : OrdinaryPairing r) : ℂ :=
  ∑ i : Fin (2 * r) → n,
    (∏ k, B k (i ((traceSites r).symm (.inr k)))
      (i ((traceSites r).symm (.inl (finRotate r k))))) * (ordinaryPairingDelta p i : ℂ)

/-- The independent genuine column network with paired labels. -/
def traceColumnNetwork {r : ℕ} (A : Fin r → Matrix n n ℂ) (q : OrdinaryPairing r) : ℂ :=
  ∑ j : Fin (2 * r) → n,
    (∏ k, A k (j ((traceSites r).symm (.inl k)))
      (j ((traceSites r).symm (.inr k)))) * (ordinaryPairingDelta q j : ℂ)

/-- The actual pairing contraction factors into two independent network
sums. No cycle-trace or norm-bound hypothesis is assumed. -/
theorem tracePairingContraction_eq_network_product {r : ℕ} (hr : 0 < r)
    (A B : Fin r → Matrix n n ℂ) (p q : OrdinaryPairing r) :
    tracePairingContraction A B p q =
      (Fintype.card n : ℂ)⁻¹ * traceRowNetwork B p * traceColumnNetwork A q := by
  unfold tracePairingContraction
  rw [← Equiv.sum_comp (traceCodeEquiv (n := n) r).symm]
  simp_rw [traceContractionCoefficient_eq_cyclic_entries hr]
  simp only [Fintype.sum_prod_type, traceRows_symm, traceCols_symm, traceCodeEquiv_symm_apply]
  unfold traceRowNetwork traceColumnNetwork
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Degree zero has no row network cycle: its contraction is the actual
normalized trace of the identity. -/
theorem tracePairingContraction_zero (A B : Fin 0 → Matrix n n ℂ)
    (p q : OrdinaryPairing 0) :
    tracePairingContraction A B p q = (Fintype.card n : ℂ)⁻¹ * (Fintype.card n : ℂ) := by
  simp [tracePairingContraction, traceContractionCoefficient, normalizedTrace,
    ordinaryPairingDelta, Matrix.trace_one]

end FreeProbability.Orthogonal

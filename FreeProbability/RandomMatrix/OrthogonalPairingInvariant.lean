import FreeProbability.RandomMatrix.OrthogonalTensorAverage

/-! # Actual invariant tensors for arbitrary ordinary pairings -/

noncomputable section
namespace FreeProbability.Orthogonal
open Matrix MeasureTheory
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Any site equivalence specifies an ordinary pairing, with crossing permitted. -/
abbrev PairingSites (r : ℕ) := Fin (2 * r) ≃ Fin r × Fin 2

/-- Repeated coordinate labels along the two sites of each pair. -/
def pairingTuple {r : ℕ} (e : PairingSites r) (f : Fin r → n) : Fin (2 * r) → n :=
  fun p => f (e p).1

/-- The genuine pairing tensor is the finite sum of actual tuple basis vectors. -/
def pairingTensor {r : ℕ} (e : PairingSites r) : EuclideanSpace ℝ (Fin (2 * r) → n) :=
  ∑ f : Fin r → n, tensorBasisVector (2 * r) (pairingTuple e f)

omit [Fintype n] in
private theorem tuple_basis_coefficient (k : ℕ) (i j : Fin k → n) :
    (tensorBasisVector k j) i = ∏ a : Fin k, if i a = j a then (1 : ℝ) else 0 := by
  change Pi.single j 1 i = _
  by_cases hij : i = j
  · subst j
    simp
  · rw [Pi.single_eq_of_ne hij]
    symm
    obtain ⟨a, ha⟩ : ∃ a, i a ≠ j a := by
      by_contra hn
      push Not at hn
      exact hij (funext hn)
    exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp [ha])

/-- Factoring a product over all sites into its genuine two-site pairing factors. -/
private theorem prod_pairing_sites {r : ℕ} (e : PairingSites r) (h : Fin (2 * r) → ℝ) :
    (∏ p, h p) = ∏ a : Fin r, h (e.symm (a, 0)) * h (e.symm (a, 1)) := by
  rw [← e.symm.prod_comp h, Fintype.prod_prod_type]
  simp only [Fin.prod_univ_two]

/-- The actual coefficients are precisely the product of paired Kronecker deltas. -/
theorem pairingTensor_coefficient {r : ℕ} (e : PairingSites r) (i : Fin (2 * r) → n) :
    (pairingTensor (n := n) e) i = ∏ a : Fin r,
      if i (e.symm (a, 0)) = i (e.symm (a, 1)) then (1 : ℝ) else 0 := by
  change (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (2 * r) → n => ℝ) i)
    (∑ f : Fin r → n, tensorBasisVector (2 * r) (pairingTuple e f)) = _
  rw [map_sum]
  change (∑ f : Fin r → n, (tensorBasisVector (2 * r) (pairingTuple e f)) i) = _
  simp_rw [tuple_basis_coefficient]
  simp_rw [prod_pairing_sites e]
  simp only [pairingTuple, Equiv.apply_symm_apply]
  rw [← Fintype.prod_sum (fun (a : Fin r) (b : n) =>
    (if i (e.symm (a, 0)) = b then (1 : ℝ) else 0) *
    (if i (e.symm (a, 1)) = b then (1 : ℝ) else 0))]
  apply Finset.prod_congr rfl
  intro a ha
  simp [mul_ite, eq_comm]

/-- The scalar coordinate product for each pair contracts by ACTUAL row orthogonality. -/
private theorem sum_row_pair (U : Group n) (i j : n) :
    (∑ b : n, U i b * U j b) = if i = j then (1 : ℝ) else 0 := by
  have h := congrFun (congrFun ((Matrix.mem_orthogonalGroup_iff n ℝ).mp U.property) i) j
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using h

/-- Every ordinary pairing tensor is ACTUALLY fixed by every orthogonal matrix.
Invariance is proved from row orthogonality and full tuple-sum factorization. -/
theorem pairingTensor_invariant {r : ℕ} (e : PairingSites r) (U : Group n) :
    (tensorPowerRepresentation (n := n) (2 * r)).action U (pairingTensor (n := n) e) =
      pairingTensor (n := n) e := by
  apply PiLp.ext
  intro i
  rw [pairingTensor_coefficient]
  change (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (2 * r) → n => ℝ) i)
    ((tensorPowerRepresentation (n := n) (2 * r)).action U
      (∑ f : Fin r → n, tensorBasisVector (2 * r) (pairingTuple e f))) = _
  rw [map_sum, map_sum]
  change (∑ f : Fin r → n,
    ((tensorPowerRepresentation (n := n) (2 * r)).action U
      (tensorBasisVector (2 * r) (pairingTuple e f))) i) = _
  simp_rw [tensorPowerRepresentation_basis_coefficient, entryMonomial, prod_pairing_sites e]
  simp only [pairingTuple, Equiv.apply_symm_apply]
  rw [← Fintype.prod_sum (fun (a : Fin r) (b : n) =>
    (U : Matrix n n ℝ) (i (e.symm (a, 0))) b *
    (U : Matrix n n ℝ) (i (e.symm (a, 1))) b)]
  simp_rw [sum_row_pair]

/-- Genuine membership in the exact invariant-tensor subspace, with no spanning premise. -/
theorem pairingTensor_mem_fixedVectors {r : ℕ} (e : PairingSites r) :
    pairingTensor (n := n) e ∈ (tensorPowerRepresentation (n := n) (2 * r)).fixedVectors :=
  pairingTensor_invariant e

/-- Actual Haar averaging fixes the genuine pairing tensor. -/
theorem tensorPowerAverage_pairingTensor {r : ℕ} (e : PairingSites r) :
    (tensorPowerRepresentation (n := n) (2 * r)).averageCLM (pairingTensor (n := n) e) =
      pairingTensor (n := n) e :=
  (tensorPowerRepresentation (n := n) (2 * r)).average_eq_self (pairingTensor_invariant e)
end FreeProbability.Orthogonal

import FreeProbability.RandomMatrix.OrthogonalPermutationNetwork
import FreeProbability.RandomMatrix.OrthogonalTraceContractions

/-! # Genuine permutation networks as products of ordered cycle traces -/

noncomputable section
open scoped Classical
namespace FreeProbability.Orthogonal
open Matrix

private theorem matrix_row_expansion {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) : M = ∑ a : n, Matrix.single a a 1 * M := by
  ext x y
  simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.single, ite_and]

private theorem ordered_matrix_product_sum {C R : Type*} [Fintype C] [Semiring R]
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

private theorem trace_row_word {n : Type*} [Fintype n] [DecidableEq n]
    {r : ℕ} (hr : 0 < r) (M : Fin r → Matrix n n ℂ) (a : Fin r → n) :
    Matrix.trace (List.ofFn (fun k => Matrix.single (a k) (a k) 1 * M k)).prod =
      ∏ k, M k (a k) (a (finRotate r k)) := by
  let : Nonempty n := ⟨a ⟨0, hr⟩⟩
  have hn : (Fintype.card n : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
  have he := traceContractionCoefficient_eq_cyclic_entries hr (fun _ => 1) M
    (fun k => (a k, a k, a k, a k))
  simp only [traceContractionCoefficient, traceCodeFactor, Matrix.one_apply, ite_true,
    one_smul, Finset.prod_const_one, mul_one, normalizedTrace] at he
  exact mul_left_cancel₀ (inv_ne_zero hn) he

/-- A genuine ordered matrix-product trace equals its cyclic entry sum,
including empty matrix dimension. Positive word length supplies a cycle. -/
theorem trace_ordered_product_eq_cyclic_sum {n : Type*} [Fintype n] [DecidableEq n]
    {r : ℕ} (hr : 0 < r) (M : Fin r → Matrix n n ℂ) :
    Matrix.trace (List.ofFn M).prod = ∑ a : Fin r → n,
      ∏ k, M k (a k) (a (finRotate r k)) := by
  have he : (List.ofFn M).prod = ∑ a : Fin r → n,
      (List.ofFn (fun k => Matrix.single (a k) (a k) 1 * M k)).prod := by
    conv_lhs => arg 1; arg 1; intro k; rw [matrix_row_expansion (M k)]
    exact ordered_matrix_product_sum r (fun k a => Matrix.single a a 1 * M k)
  rw [he, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact trace_row_word hr M a

variable {α : Type*} [Fintype α] (σ : Equiv.Perm α)

private theorem orbit_next_enumeration (c : PermutationOrbitIndex σ)
    (k : Fin (permutationOrbitFinset σ c).card) :
    permutationOrbitNext σ c (permutationOrbitEnumeration σ c k) =
      permutationOrbitEnumeration σ c (finRotate _ k) := by
  apply Subtype.ext
  exact (permutationOrbitEnumeration_rotate σ c k).symm

/-- One actual permutation orbit network is its genuine ordered cycle trace.
The enumeration follows actual powers and includes fixed singleton orbits. -/
theorem permutationOrbitNetwork_eq_trace {n : Type*} [Fintype n] [DecidableEq n]
    (M : α → Matrix n n ℂ) (c : PermutationOrbitIndex σ) :
    permutationOrbitNetwork σ M c = Matrix.trace
      (List.ofFn (fun k => M (permutationOrbitEnumeration σ c k).val)).prod := by
  rw [trace_ordered_product_eq_cyclic_sum (permutationOrbit_length_pos σ c)]
  unfold permutationOrbitNetwork
  rw [← Equiv.sum_comp (Equiv.arrowCongr (permutationOrbitEnumeration σ c).symm (Equiv.refl n)).symm]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Equiv.prod_comp (permutationOrbitEnumeration σ c)]
  apply Finset.prod_congr rfl
  intro k _
  rw [orbit_next_enumeration]
  simp only [Equiv.arrowCongr_symm, Equiv.arrowCongr_apply, Equiv.refl_symm,
    Equiv.symm_symm, Function.comp_apply, Equiv.refl_apply, Equiv.symm_apply_apply]

/-- The ACTUAL finite permutation network is the product of genuine ordered
cycle traces over ALL product orbits, with no trace identity premise. -/
theorem permutationNetwork_eq_prod_cycle_traces {n : Type*} [Fintype n] [DecidableEq n]
    (M : α → Matrix n n ℂ) :
    permutationNetwork σ M = ∏ c : PermutationOrbitIndex σ, Matrix.trace
      (List.ofFn (fun k => M (permutationOrbitEnumeration σ c k).val)).prod := by
  rw [permutationNetwork_eq_prod_orbit_networks]
  simp_rw [permutationOrbitNetwork_eq_trace]

/-- An empty index set contributes the genuine empty product one. -/
theorem permutationNetwork_empty_index [IsEmpty α] {n : Type*} [Fintype n]
    (M : α → Matrix n n ℂ) : permutationNetwork σ M = 1 := by
  simp [permutationNetwork]

/-- An empty color dimension makes every nonempty network zero. -/
theorem permutationNetwork_empty_dimension [Nonempty α] {n : Type*} [Fintype n] [IsEmpty n]
    (M : α → Matrix n n ℂ) : permutationNetwork σ M = 0 := by
  simp [permutationNetwork]

/-- The identity permutation retains EVERY fixed singleton trace. -/
theorem permutationNetwork_identity {n : Type*} [Fintype n]
    (M : α → Matrix n n ℂ) : permutationNetwork (1 : Equiv.Perm α) M = ∏ a, Matrix.trace (M a) := by
  unfold permutationNetwork
  simp only [Equiv.Perm.one_apply, Matrix.trace]
  exact (Fintype.prod_sum (fun a b => M a b b)).symm

end FreeProbability.Orthogonal

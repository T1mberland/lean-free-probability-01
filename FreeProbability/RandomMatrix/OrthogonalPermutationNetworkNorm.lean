import FreeProbability.RandomMatrix.OrthogonalPermutationNetworkTrace
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! # Genuine Euclidean operator-norm bounds for actual permutation networks -/

noncomputable section
open scoped Classical Matrix.Norms.L2Operator InnerProductSpace
namespace FreeProbability.Orthogonal
open Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem diagonal_entry_le_Euclidean_opNorm (M : Matrix n n ℂ) (i : n) :
    ‖M i i‖ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) M‖ := by
  let e : EuclideanSpace ℂ n := EuclideanSpace.single i 1
  have he : inner ℂ e (Matrix.toEuclideanCLM (𝕜 := ℂ) M e) = M i i := by
    simp [e, EuclideanSpace.inner_single_left, EuclideanSpace.single, Matrix.mulVec, dotProduct]
  have hn : ‖e‖ = 1 := by simp [e, PiLp.norm_single]
  rw [← he]
  have hi := norm_inner_le_norm (𝕜 := ℂ) e (Matrix.toEuclideanCLM (𝕜 := ℂ) M e)
  have ho := (Matrix.toEuclideanCLM (𝕜 := ℂ) M).le_opNorm e
  rw [hn, one_mul] at hi
  rw [hn, mul_one] at ho
  exact hi.trans ho

/-- Ordinary complex trace is bounded using the ACTUAL Euclidean operator
norm, not the default entrywise matrix norm. -/
theorem trace_norm_le_card_mul_Euclidean_opNorm (M : Matrix n n ℂ) :
    ‖Matrix.trace M‖ ≤ (Fintype.card n : ℝ) * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) M‖ := by
  unfold Matrix.trace
  apply (norm_sum_le _ _).trans
  calc
    ∑ i, ‖M i i‖ ≤ ∑ _i : n, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) M‖ :=
      Finset.sum_le_sum (fun i _ => diagonal_entry_le_Euclidean_opNorm M i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Actual ordered cycle traces have the dimension-times-product operator
bound, including empty matrix dimension. Positive length avoids a norm-one
assumption for a zero-dimensional identity operator. -/
theorem trace_ordered_product_norm_le {r : ℕ} (hr : 0 < r)
    (M : Fin r → Matrix n n ℂ) :
    ‖Matrix.trace (List.ofFn M).prod‖ ≤ (Fintype.card n : ℝ) *
      ∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (M k)‖ := by
  have hne : List.ofFn M ≠ [] := by
    intro h
    have he := congrArg List.length h
    simp only [List.length_ofFn, List.length_nil] at he
    omega
  have hp := List.norm_prod_le' hne
  have hpn : ‖(List.ofFn M).prod‖ ≤ ∏ k, ‖M k‖ := by
    simpa only [List.map_ofFn, List.prod_ofFn, Function.comp_def] using hp
  exact (trace_norm_le_card_mul_Euclidean_opNorm _).trans
    (mul_le_mul_of_nonneg_left (by simpa only [Matrix.cstar_norm_def] using hpn) (by positivity))

variable {α : Type*} [Fintype α] (σ : Equiv.Perm α)

private theorem product_orbit_enumerations {R : Type*} [CommMonoid R] (f : α → R) :
    (∏ c : PermutationOrbitIndex σ, ∏ k, f (permutationOrbitEnumeration σ c k).val) = ∏ a, f a := by
  calc
    _ = ∏ c : PermutationOrbitIndex σ, ∏ a : PermutationOrbit σ c, f a.val := by
      apply Finset.prod_congr rfl
      intro c _
      exact Equiv.prod_comp (permutationOrbitEnumeration σ c) (fun a : PermutationOrbit σ c => f a.val)
    _ = ∏ a : (Σ c : PermutationOrbitIndex σ, PermutationOrbit σ c), f a.2.val := by
      rw [Fintype.prod_sigma]
    _ = _ := Equiv.prod_comp (permutationOrbitSigmaEquiv σ) f

/-- The actual network has one dimension factor per genuine permutation orbit
and one Euclidean operator norm per actual matrix label. ALL empty dimensions
and index types are covered without additional hypotheses. -/
theorem permutationNetwork_norm_le (M : α → Matrix n n ℂ) :
    ‖permutationNetwork σ M‖ ≤ (Fintype.card n : ℝ) ^ Fintype.card (PermutationOrbitIndex σ) *
      ∏ a, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (M a)‖ := by
  rw [permutationNetwork_eq_prod_cycle_traces]
  apply (Finset.norm_prod_le _ _).trans
  calc
    ∏ c : PermutationOrbitIndex σ,
        ‖Matrix.trace (List.ofFn (fun k => M (permutationOrbitEnumeration σ c k).val)).prod‖ ≤
        ∏ c : PermutationOrbitIndex σ, (Fintype.card n : ℝ) *
          ∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (M (permutationOrbitEnumeration σ c k).val)‖ := by
      apply Finset.prod_le_prod₀
      · intro c _; positivity
      · intro c _
        exact trace_ordered_product_norm_le (permutationOrbit_length_pos σ c) _
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
      exact congrArg (fun t : ℝ => (Fintype.card n : ℝ) ^ Fintype.card (PermutationOrbitIndex σ) * t)
        (product_orbit_enumerations σ (fun a : α => ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (M a)‖))

/-- A genuine fixed singleton cycle with zero ordinary trace kills the actual
network. No additional network cancellation premise is used. -/
theorem permutationNetwork_eq_zero_of_fixed_trace_zero (M : α → Matrix n n ℂ)
    (a : α) (ha : σ a = a) (hz : Matrix.trace (M a) = 0) : permutationNetwork σ M = 0 := by
  let c : PermutationOrbitIndex σ := Quotient.mk _ a
  have hs : c.out = a := (Quotient.exact (Quotient.out_eq c)).eq_of_right ha
  have hset : permutationOrbitFinset σ c = {a} := by
    ext b
    simp only [permutationOrbitFinset, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton, hs]
    constructor
    · intro h
      exact (h.eq_of_left ha).symm
    · rintro rfl
      exact Equiv.Perm.SameCycle.rfl
  have hcard : (permutationOrbitFinset σ c).card = 1 := by rw [hset]; exact Finset.card_singleton a
  have he (k : Fin (permutationOrbitFinset σ c).card) :
      (permutationOrbitEnumeration σ c k).val = a := by
    have hk : k.val = 0 := by have := k.isLt; omega
    rw [permutationOrbitEnumeration_apply, hk, pow_zero, Equiv.Perm.one_apply, hs]
  rw [permutationNetwork_eq_prod_cycle_traces]
  apply Finset.prod_eq_zero (Finset.mem_univ c)
  simp_rw [he]
  simpa only [List.ofFn_const, hcard, List.replicate_one, List.prod_singleton] using hz

end FreeProbability.Orthogonal

import FreeProbability.Fock.ClosedGeneratedState

/-! # The exact norm of the concrete semicircular generators -/

noncomputable section
open scoped Classical InnerProductSpace BigOperators

namespace FreeProbability.Fock

variable {I : Type*}

/-- A finite constant-amplitude vector along a one-letter word chain. -/
def chainVector (i : I) (n : ℕ) : WordSpace I :=
  ∑ k ∈ Finset.range n, word (List.replicate k i)

private theorem replicate_eq_iff (i : I) (k m : ℕ) :
    List.replicate k i = List.replicate m i ↔ k = m := by
  constructor
  · intro h
    simpa using congrArg List.length h
  · rintro rfl; rfl

@[simp] theorem inner_chainVector_word (i : I) (n m : ℕ) :
    inner ℂ (chainVector i n) (word (List.replicate m i)) = if m < n then 1 else 0 := by
  unfold chainVector
  simp only [sum_inner, inner_word, replicate_eq_iff]
  simp

/-- Exact squared norm of the finite chain vector. -/
theorem norm_chainVector_sq (i : I) (n : ℕ) : ‖chainVector i n‖ ^ 2 = n := by
  have h : inner ℂ (chainVector i n) (chainVector i n) = n := by
    change inner ℂ (chainVector i n) (∑ k ∈ Finset.range n, word (List.replicate k i)) = n
    rw [inner_sum]
    calc
      _ = ∑ k ∈ Finset.range n, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [inner_chainVector_word, ite_eq_left (Finset.mem_range.mp hk)]
      _ = n := by simp
  rw [inner_self_eq_norm_sq_to_K] at h
  have hr := congrArg Complex.re h
  change (Complex.ofReal ‖chainVector i n‖ ^ 2).re = (n : ℝ) at hr
  simpa [pow_two] using hr

/-- Each of the `n` edges contributes one to the creation Rayleigh form. -/
theorem inner_chainVector_creation (i : I) (n : ℕ) :
    inner ℂ (chainVector i (n + 1)) (creation i (chainVector i (n + 1))) = n := by
  simp only [chainVector, map_sum, inner_sum, creation_word, ← List.replicate_succ]
  change (∑ k ∈ Finset.range (n + 1),
    inner ℂ (chainVector i (n + 1)) (word (List.replicate (k + 1) i))) = n
  simp only [inner_chainVector_word]
  rw [Finset.sum_range_succ]
  have hsum : (∑ k ∈ Finset.range n, (if k + 1 < n + 1 then (1 : ℂ) else 0)) = n := by
    have h : ∀ k ∈ Finset.range n, k + 1 < n + 1 := by
      intro k hk
      simpa using Finset.mem_range.mp hk
    calc
      _ = ∑ k ∈ Finset.range n, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [ite_eq_left (h k hk)]
      _ = n := by simp
  rw [hsum]
  simp

/-- The finite Rayleigh numerator equals twice the number of chain edges. -/
theorem inner_chainVector_semicircular (i : I) (n : ℕ) :
    inner ℂ (chainVector i (n + 1)) (semicircular i (chainVector i (n + 1))) = 2 * n := by
  have h := inner_chainVector_creation i n
  have ha : inner ℂ (chainVector i (n + 1))
      (annihilation i (chainVector i (n + 1))) = n := by
    rw [annihilation, ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm, h]
    simp
  simp [semicircular, inner_add_right, h, ha, two_mul]

/-- Quantitative finite-depth Rayleigh bound approaching the spectral edge two. -/
theorem semicircular_rayleigh_bound (i : I) (n : ℕ) :
    2 * (n : ℝ) ≤ ‖semicircular i‖ * ((n : ℝ) + 1) := by
  let x := chainVector i (n + 1)
  calc
    2 * (n : ℝ) = (inner ℂ x (semicircular i x)).re := by
      rw [inner_chainVector_semicircular]
      simp
    _ ≤ ‖x‖ * ‖semicircular i x‖ := re_inner_le_norm (𝕜 := ℂ) _ _
    _ ≤ ‖x‖ * (‖semicircular i‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left ((semicircular i).le_opNorm x) (norm_nonneg x)
    _ = ‖semicircular i‖ * ‖x‖ ^ 2 := by ring
    _ = ‖semicircular i‖ * ((n : ℝ) + 1) := by
      rw [norm_chainVector_sq]
      simp

/-- Each concrete canonical semicircular operator has norm exactly two. -/
@[simp] theorem norm_semicircular (i : I) : ‖semicircular i‖ = 2 := by
  apply le_antisymm (norm_semicircular_le_two i)
  by_contra h
  have hlt : ‖semicircular i‖ < 2 := lt_of_not_ge h
  obtain ⟨n, hn⟩ := exists_nat_gt (‖semicircular i‖ / (2 - ‖semicircular i‖))
  have hn' := (div_lt_iff₀ (sub_pos.mpr hlt)).mp hn
  have hr := semicircular_rayleigh_bound i n
  nlinarith

end FreeProbability.Fock


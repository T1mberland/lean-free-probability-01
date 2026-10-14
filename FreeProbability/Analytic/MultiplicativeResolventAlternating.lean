import FreeProbability.Algebraic.Freeness
import Mathlib.Data.List.Basic

/-! # Exact alternating centered power moments -/

namespace FreeProbability
variable {𝕜 A I : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]

private def pairWord (i j : I) (x y : A) (n : ℕ) : List (I × A) :=
  (List.replicate n [(i, x), (j, y)]).flatten

omit [Ring A] in
private theorem pairWord_chain (i j : I) (hij : i ≠ j) (x y : A) (n : ℕ) :
    (pairWord i j x y n).IsChain (fun a b => a.1 ≠ b.1) := by
  apply (List.isChain_flatten (by simp)).mpr
  constructor
  · intro l hl
    obtain ⟨_, rfl⟩ := List.mem_replicate.mp hl
    simpa using hij
  · apply List.isChain_replicate_of_rel
    simp [Ne.symm hij]

private theorem pairWord_prod (i j : I) (x y : A) (n : ℕ) :
    ((pairWord i j x y n).map Prod.snd).prod = (x * y) ^ n := by
  simp [pairWord, List.map_flatten, List.map_replicate, List.prod_flatten]

namespace FreelyIndependent
variable {φ : ProbabilitySpace 𝕜 A} {B : I → Subalgebra 𝕜 A}

/-- Every positive power of a product of two centered free elements has zero
expectation, without trace or positivity assumptions. -/
theorem expectation_pow_centered_pair (hf : FreelyIndependent φ B)
    {i j : I} (hij : i ≠ j) (x y : A) (hx : x ∈ B i) (hy : y ∈ B j)
    (hzx : φ.expectation x = 0) (hzy : φ.expectation y = 0)
    (n : ℕ) (hn : 0 < n) : φ.expectation ((x * y) ^ n) = 0 := by
  have hne : pairWord i j x y n ≠ [] := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    simp [pairWord, List.replicate_succ]
  have hmem : ∀ a ∈ pairWord i j x y n, a.2 ∈ B a.1 := by
    intro a ha
    obtain ⟨l, hl, hal⟩ := List.mem_flatten.mp ha
    obtain ⟨_, rfl⟩ := List.mem_replicate.mp hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hal
    rcases hal with rfl | rfl
    · exact hx
    · exact hy
  have hzero : ∀ a ∈ pairWord i j x y n, φ.expectation a.2 = 0 := by
    intro a ha
    obtain ⟨l, hl, hal⟩ := List.mem_flatten.mp ha
    obtain ⟨_, rfl⟩ := List.mem_replicate.mp hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hal
    rcases hal with rfl | rfl
    · exact hzx
    · exact hzy
  have h := hf _ hne (pairWord_chain i j hij x y n) hmem hzero
  rw [pairWord_prod] at h
  exact h
/-- Alternating odd words ending in the first centered element also vanish. -/
theorem expectation_pow_centered_pair_mul (hf : FreelyIndependent φ B)
    {i j : I} (hij : i ≠ j) (x y : A) (hx : x ∈ B i) (hy : y ∈ B j)
    (hzx : φ.expectation x = 0) (hzy : φ.expectation y = 0)
    (n : ℕ) : φ.expectation ((x * y) ^ n * x) = 0 := by
  let w := pairWord i j x y n ++ [(i, x)]
  have hc : w.IsChain (fun a b => a.1 ≠ b.1) := by
    by_cases hn : n = 0
    · simp [w, pairWord, hn]
    · apply (pairWord_chain i j hij x y n).append (by simp)
      simp only [pairWord, List.getLast?_flatten_replicate hn, List.getLast?_cons,
 List.head?_cons, Option.mem_def]
      intro a ha b hb
      cases ha
      cases hb
      exact hij.symm
  have hmem : ∀ a ∈ w, a.2 ∈ B a.1 := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨l, hl, hal⟩ := List.mem_flatten.mp ha
      obtain ⟨_, rfl⟩ := List.mem_replicate.mp hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hal
      rcases hal with rfl | rfl
      · exact hx
      · exact hy
    · have he := List.mem_singleton.mp ha
      simpa only [he] using hx
  have hzero : ∀ a ∈ w, φ.expectation a.2 = 0 := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨l, hl, hal⟩ := List.mem_flatten.mp ha
      obtain ⟨_, rfl⟩ := List.mem_replicate.mp hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hal
      rcases hal with rfl | rfl
      · exact hzx
      · exact hzy
    · have he := List.mem_singleton.mp ha
      simpa only [he] using hzx
  have h := hf w (by simp [w]) hc hmem hzero
  simpa only [w, List.map_append, List.prod_append, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, pairWord_prod] using h

/-- Alternating odd words starting in the second centered element vanish. -/
theorem expectation_mul_pow_centered_pair (hf : FreelyIndependent φ B)
    {i j : I} (hij : i ≠ j) (x y : A) (hx : x ∈ B i) (hy : y ∈ B j)
    (hzx : φ.expectation x = 0) (hzy : φ.expectation y = 0)
    (n : ℕ) : φ.expectation (y * (x * y) ^ n) = 0 := by
  have h := hf.expectation_pow_centered_pair_mul hij.symm y x hy hx hzy hzx n
  rw [mul_pow_mul] at h
  exact h

/-- The even alternating word with both additional endpoints vanishes. -/
theorem expectation_mul_pow_centered_pair_mul (hf : FreelyIndependent φ B)
    {i j : I} (hij : i ≠ j) (x y : A) (hx : x ∈ B i) (hy : y ∈ B j)
    (hzx : φ.expectation x = 0) (hzy : φ.expectation y = 0)
    (n : ℕ) : φ.expectation (y * (x * y) ^ n * x) = 0 := by
  have h := hf.expectation_pow_centered_pair hij.symm y x hy hx hzy hzx (n + 1) (by omega)
  rw [pow_succ, ← mul_assoc, mul_pow_mul] at h
  exact h
/-- The complete sandwich moment sequence: all positive powers vanish,
and the zeroth term is exactly the product of the scalar means. -/
theorem expectation_centered_pair_sandwich_pow (hf : FreelyIndependent φ B)
    {i j : I} (hij : i ≠ j) (x y : A) (hx : x ∈ B i) (hy : y ∈ B j)
    (hzx : φ.expectation x = 0) (hzy : φ.expectation y = 0)
    (c d : 𝕜) (n : ℕ) :
    φ.expectation ((y + c • 1) * (x * y) ^ n * (x + d • 1)) =
      if n = 0 then c * d else 0 := by
  cases n with
  | zero =>
    have hxy : φ.expectation (y * x) = 0 := by
      rw [hf.expectation_mul hij.symm hy hx, hzy, hzx, mul_zero]
    simp only [pow_zero, mul_one, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
      one_mul, mul_one, map_add, map_smul, smul_eq_mul,
      hxy, hzx, hzy, φ.expectation_one, mul_zero, zero_add, add_zero,
      ite_true]
    exact mul_comm d c
  | succ n =>
    have h0 := hf.expectation_pow_centered_pair hij x y hx hy hzx hzy (n + 1) (by omega)
    have h1 := hf.expectation_pow_centered_pair_mul hij x y hx hy hzx hzy (n + 1)
    have h2 := hf.expectation_mul_pow_centered_pair hij x y hx hy hzx hzy (n + 1)
    have h3 := hf.expectation_mul_pow_centered_pair_mul hij x y hx hy hzx hzy (n + 1)
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
      map_add, map_smul, smul_eq_mul, h0, h1, h2, h3,
      mul_zero, zero_add, Nat.succ_ne_zero, ite_false]
end FreelyIndependent
end FreeProbability

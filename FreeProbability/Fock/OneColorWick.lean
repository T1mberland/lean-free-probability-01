import FreeProbability.Fock.SemicircularNorm

/-!
# One-color Wick recursion and creation on foreign words

These polynomials provide the centered one-generator basis needed for a direct
proof of freeness. The action lemma below is unconditional on the concrete
operators; the nonmatching first letter prevents annihilation at the boundary.
-/

noncomputable section
open scoped Classical

namespace FreeProbability.Fock

variable {I : Type*}

/-- The degree-`n` monic Wick polynomial in a single semicircular generator. -/
def oneColorWick (i : I) (n : ℕ) : WordSpace I →L[ℂ] WordSpace I :=
  wick (List.replicate n i)

@[simp] theorem oneColorWick_zero (i : I) : oneColorWick i 0 = 1 := rfl

@[simp] theorem oneColorWick_one (i : I) : oneColorWick i 1 = semicircular i :=
  wick_singleton i

/-- The Chebyshev recurrence holds as an equality of bounded operators. -/
theorem oneColorWick_succ_succ (i : I) (n : ℕ) :
    oneColorWick i (n + 2) = semicircular i * oneColorWick i (n + 1) - oneColorWick i n := by
  simp [oneColorWick, List.replicate_succ, wick]

/-- A one-color Wick polynomial simply prefixes its color block to a foreign-headed word. -/
theorem oneColorWick_word (i : I) (n : ℕ) (w : List I)
    (hw : ∀ j v, w = j :: v → i ≠ j) :
    oneColorWick i n (word w) = word (List.replicate n i ++ w) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
    simp only [oneColorWick_one, semicircular, add_apply, creation_word]
    cases w with
    | nil => simp
    | cons j v => simp [annihilation_word, hw j v rfl]
  | more n hn hn₁ =>
    rw [oneColorWick_succ_succ]
    simp only [sub_apply, mul_apply_eq_comp, hn, hn₁]
    rw [List.replicate_succ, List.cons_append]
    simp only [semicircular, add_apply, creation_word, annihilation_word ]
    simp [List.replicate_succ]

@[simp] theorem vacuumExpectation_oneColorWick (i : I) (n : ℕ) :
    vacuumExpectation (oneColorWick i n) = if n = 0 then 1 else 0 := by
  change inner ℂ vacuum (wick (List.replicate n i) vacuum) = _
  rw [wick_vacuum]
  simp only [vacuum, inner_word]
  cases n <;> simp

/-- The linear span of the one-color Wick polynomials. -/
def oneColorSpan (i : I) : Submodule ℂ (WordSpace I →L[ℂ] WordSpace I) :=
  Submodule.span ℂ (Set.range (oneColorWick i))

theorem oneColorWick_mem_span (i : I) (n : ℕ) : oneColorWick i n ∈ oneColorSpan i :=
  Submodule.subset_span ⟨n, rfl⟩

/-- Multiplication by the generator preserves the one-color Wick span. -/
theorem semicircular_mul_mem_oneColorSpan (i : I)
    {T : WordSpace I →L[ℂ] WordSpace I} (hT : T ∈ oneColorSpan i) :
    semicircular i * T ∈ oneColorSpan i := by
  induction hT using Submodule.span_induction with
  | mem T hT =>
    obtain ⟨n, rfl⟩ := hT
    cases n with
    | zero => simpa using oneColorWick_mem_span i 1
    | succ n =>
      have heq : semicircular i * oneColorWick i (n + 1) =
          oneColorWick i (n + 2) + oneColorWick i n := by
        rw [oneColorWick_succ_succ]
        abel
      rw [heq]
      exact (oneColorSpan i).add_mem (oneColorWick_mem_span i _) (oneColorWick_mem_span i _)
  | zero => simp
  | add T U hT hU ihT ihU => simpa [mul_add] using (oneColorSpan i).add_mem ihT ihU
  | smul c T hT ihT =>
    have heq : semicircular i * (c • T) = c • (semicircular i * T) := by
      ext f
      simp [mul_apply_eq_comp]
    rw [heq]
    exact (oneColorSpan i).smul_mem c ihT

private theorem oneColorWick_mul_mem_span (i : I) (n : ℕ)
    {T : WordSpace I →L[ℂ] WordSpace I} (hT : T ∈ oneColorSpan i) :
    oneColorWick i n * T ∈ oneColorSpan i := by
  induction n using Nat.twoStepInduction with
  | zero => simpa using hT
  | one => simpa using semicircular_mul_mem_oneColorSpan i hT
  | more n hn hn₁ =>
    rw [oneColorWick_succ_succ, sub_mul, mul_assoc]
    exact (oneColorSpan i).sub_mem (semicircular_mul_mem_oneColorSpan i hn₁) hn

/-- The Wick span is an actual unital algebra, not merely a vector subspace. -/
def oneColorAlgebra (i : I) : Subalgebra ℂ (WordSpace I →L[ℂ] WordSpace I) where
  carrier := oneColorSpan i
  zero_mem' := (oneColorSpan i).zero_mem
  add_mem' := (oneColorSpan i).add_mem
  one_mem' := by simpa using oneColorWick_mem_span i 0
  mul_mem' := by
    intro T U hT hU
    induction hT using Submodule.span_induction with
    | mem T hT =>
      obtain ⟨n, rfl⟩ := hT
      exact oneColorWick_mul_mem_span i n hU
    | zero => simp
    | add T V hT hV ihT ihV => simpa [add_mul] using (oneColorSpan i).add_mem ihT ihV
    | smul c T hT ihT =>
      have heq : (c • T) * U = c • (T * U) := by
        ext f
        simp [mul_apply_eq_comp]
      rw [heq]
      exact (oneColorSpan i).smul_mem c ihT
  algebraMap_mem' c := by
    rw [Algebra.algebraMap_eq_smul_one]
    apply (oneColorSpan i).smul_mem
    simpa using oneColorWick_mem_span i 0

/-- Every polynomial in a generator is a finite linear combination of its Wick polynomials. -/
theorem mem_oneColorSpan_of_mem_adjoin (i : I)
    {T : WordSpace I →L[ℂ] WordSpace I}
    (hT : T ∈ Algebra.adjoin ℂ ({semicircular i} : Set _)) : T ∈ oneColorSpan i := by
  have hle : Algebra.adjoin ℂ ({semicircular i} : Set _) ≤ oneColorAlgebra i :=
    Algebra.adjoin_singleton_le (by
      change semicircular i ∈ oneColorSpan i
      simpa using oneColorWick_mem_span i 1)
  exact hle hT

private theorem zero_smul_operator (T : WordSpace I →L[ℂ] WordSpace I) : (0 : ℂ) • T = 0 := by
  ext f
  simp

/-- Positive-degree Wick polynomials span the centered part of the one-color algebra. -/
def positiveOneColorSpan (i : I) : Submodule ℂ (WordSpace I →L[ℂ] WordSpace I) :=
  Submodule.span ℂ (Set.range (fun n => oneColorWick i (n + 1)))

/-- Subtracting the actual vacuum mean removes exactly the degree-zero Wick coefficient. -/
theorem center_mem_positiveOneColorSpan (i : I)
    {T : WordSpace I →L[ℂ] WordSpace I} (hT : T ∈ oneColorSpan i) :
    T - vacuumExpectation T • (1 : WordSpace I →L[ℂ] WordSpace I) ∈ positiveOneColorSpan i := by
  induction hT using Submodule.span_induction with
  | mem T hT =>
    obtain ⟨n, rfl⟩ := hT
    cases n with
    | zero => simp
    | succ n =>
      simpa [zero_smul_operator, positiveOneColorSpan] using (Submodule.subset_span (R := ℂ) (s := Set.range (fun n => oneColorWick i (n + 1))) ⟨n, rfl⟩)
  | zero => simp [vacuumExpectation, zero_smul_operator]
  | add T U hT hU ihT ihU =>
    have hτ : vacuumExpectation (T + U) = vacuumExpectation T + vacuumExpectation U :=
      map_add vacuumLinear T U
    have heq : T + U - (vacuumExpectation T + vacuumExpectation U) • (1 : WordSpace I →L[ℂ] WordSpace I) =
        (T - vacuumExpectation T • (1 : WordSpace I →L[ℂ] WordSpace I)) + (U - vacuumExpectation U • (1 : WordSpace I →L[ℂ] WordSpace I)) := by
      ext f
      simp only [sub_apply, add_apply, smul_apply]
      rw [add_smul]
      abel_nf
    rw [hτ, heq]
    exact (positiveOneColorSpan i).add_mem ihT ihU
  | smul c T hT ihT =>
    have hτ : vacuumExpectation (c • T) = c • vacuumExpectation T :=
      map_smul vacuumLinear c T
    rw [hτ]
    have heq : c • T - (c • vacuumExpectation T) • (1 : WordSpace I →L[ℂ] WordSpace I) = c • (T - vacuumExpectation T • (1 : WordSpace I →L[ℂ] WordSpace I)) := by
      simp [smul_sub, smul_smul, smul_eq_mul]
    rw [heq]
    exact (positiveOneColorSpan i).smul_mem c ihT

/-- An arbitrary centered polynomial, not only a selected Wick word, has a positive-degree expansion. -/
theorem centered_mem_positiveOneColorSpan (i : I)
    {T : WordSpace I →L[ℂ] WordSpace I}
    (hT : T ∈ Algebra.adjoin ℂ ({semicircular i} : Set _))
    (hzero : vacuumExpectation T = 0) : T ∈ positiveOneColorSpan i := by
  simpa [hzero, zero_smul_operator] using center_mem_positiveOneColorSpan i (mem_oneColorSpan_of_mem_adjoin i hT)

end FreeProbability.Fock



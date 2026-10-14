import FreeProbability.OperatorValued.MatrixTensorCalculus

/-! # Free differentiation of actual matrix polynomial powers -/

noncomputable section
open scoped Classical
namespace FreeProbability

variable {𝕜 I n : Type*} [Field 𝕜] [Fintype n] [DecidableEq n]

omit [Fintype n] in
@[simp] theorem matrixFreeDifferenceQuotient_one (i : I) :
    matrixFreeDifferenceQuotient i (1 : Matrix n n (WordPolynomial 𝕜 I)) = 0 := by
  ext r c
  simp [matrixFreeDifferenceQuotient, Matrix.one_apply, apply_ite]

/-- The derivative sums every possible cut in the matrix power, with the
ordered prefix on the first tensor factor and suffix on the second. -/
theorem matrixFreeDifferenceQuotient_pow (i : I)
    (P : Matrix n n (WordPolynomial 𝕜 I)) (k : ℕ) :
    matrixFreeDifferenceQuotient i (P ^ k) =
      ∑ j ∈ Finset.range k,
        matrixTensorLeft (P ^ j)
          (matrixTensorRight (P ^ (k - 1 - j)) (matrixFreeDifferenceQuotient i P)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, matrixFreeDifferenceQuotient_leibniz, ih, map_sum]
    rw [Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, matrixTensorRight_one]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hjk : j < k := Finset.mem_range.mp hj
    rw [← matrixTensorLeft_right, ← matrixTensorRight_mul, ← pow_succ]
    have he : k - 1 - j + 1 = k - j := by omega
    rw [he]

end FreeProbability

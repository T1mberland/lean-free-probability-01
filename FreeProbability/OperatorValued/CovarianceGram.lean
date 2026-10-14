import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap

/-! # Genuine finite Gram positivity for arbitrary CP covariance -/
noncomputable section
open scoped BigOperators CStarAlgebra
namespace FreeProbability
variable {B n : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] [Fintype n]

/-- The ordered, noncommutative Gram matrix of an arbitrary finite family. -/
def cstarGramMatrix (a : n → B) : CStarMatrix n n B := fun i j => star (a i) * a j

theorem cstarGramMatrix_nonneg (a : n → B) : 0 ≤ cstarGramMatrix a := by
  classical
  cases isEmpty_or_nonempty n with
  | inl hn =>
    let := hn
    have hz : cstarGramMatrix a = 0 := by
      ext i j
      exact isEmptyElim i
    rw [hz]
  | inr hn =>
    let := hn
    let i₀ : n := Classical.choice hn
    let R : CStarMatrix n n B := fun i j => if i = i₀ then a j else 0
    have hR : star R * R = cstarGramMatrix a := by
      ext i j
      change (∑ k, star (R k i) * R k j) = star (a i) * a j
      simp [R]
    rw [← hR]
    exact star_mul_self_nonneg R

/-- Any CP covariance sends every actual finite Gram matrix to a positive matrix. -/
theorem cp_covariance_gram_nonneg (η : B →CP B) (a : n → B) :
    0 ≤ (cstarGramMatrix a).map η :=
  η.map_cstarMatrix_nonneg _ (cstarGramMatrix_nonneg a)

/-- The ordered coefficient quadratic form of an actual matrix star square is positive. -/
theorem cstarMatrix_starSquare_quadratic_nonneg (Y : CStarMatrix n n B) (b : n → B) :
    0 ≤ ∑ i, ∑ j, star (b i) * (star Y * Y) i j * b j := by
  classical
  have he : (∑ i, ∑ j, star (b i) * (star Y * Y) i j * b j) =
      ∑ k, star (∑ i, Y k i * b i) * (∑ j, Y k j * b j) := by
    change (∑ i, ∑ j, star (b i) * (∑ k, star (Y k i) * Y k j) * b j) = _
    calc
      _ = ∑ i, ∑ j, ∑ k, star (Y k i * b i) * (Y k j * b j) := by
        simp only [Finset.mul_sum, Finset.sum_mul, star_mul, mul_assoc]
      _ = ∑ i, ∑ k, ∑ j, star (Y k i * b i) * (Y k j * b j) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_comm]
      _ = ∑ k, ∑ i, ∑ j, star (Y k i * b i) * (Y k j * b j) := Finset.sum_comm
      _ = _ := by
        simp only [star_sum, Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.sum_comm]
  rw [he]
  exact Finset.sum_nonneg fun k _ => star_mul_self_nonneg _

/-- Genuine positive C-star matrices have positive coefficient quadratic forms. -/
theorem cstarMatrix_quadratic_nonneg (M : CStarMatrix n n B) (hM : 0 ≤ M) (b : n → B) :
    0 ≤ ∑ i, ∑ j, star (b i) * M i j * b j := by
  classical
  rw [StarOrderedRing.nonneg_iff] at hM
  induction hM using AddSubmonoid.closure_induction with
  | mem M h =>
    obtain ⟨Y, rfl⟩ := h
    exact cstarMatrix_starSquare_quadratic_nonneg Y b
  | zero => simp
  | add M N _ _ hM hN =>
    change 0 ≤ ∑ i, ∑ j, star (b i) * (M i j + N i j) * b j
    simp only [mul_add, add_mul, Finset.sum_add_distrib]
    exact add_nonneg hM hN

/-- Arbitrary CP covariance satisfies the full ordered coefficient Gram inequality. -/
theorem cp_covariance_quadratic_nonneg (η : B →CP B) (a b : n → B) :
    0 ≤ ∑ i, ∑ j, star (b i) * η (star (a i) * a j) * b j :=
  cstarMatrix_quadratic_nonneg _ (cp_covariance_gram_nonneg η a) b

end FreeProbability

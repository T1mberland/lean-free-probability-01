import FreeProbability.Fock.WickSuffixGramFibers

/-! # Genuine positive finite suffix-cut Gram operators -/
noncomputable section
open scoped Classical BigOperators ComplexOrder
namespace FreeProbability.Fock
variable {I ν : Type*} [Fintype ν]

/-- The actual matrix amplitude restricted to a fixed terminal-cut fiber. -/
def matrixCutAmplitude (S : Finset (List I)) (C : List I → Matrix ν ν ℂ)
    (h : ℕ) (s : List I) : CStarMatrix ν ν (WordSpace I →L[ℂ] WordSpace I) :=
  ∑ u ∈ S, if u.drop h = s then matrixWickTerm (C u) (u.take h) else 0

/-- Actual finite Gram sum at a prefix degree. -/
def matrixCutGram (S : Finset (List I)) (C : List I → Matrix ν ν ℂ) (h : ℕ) :
    CStarMatrix ν ν (WordSpace I →L[ℂ] WordSpace I) :=
  ∑ s ∈ @Finset.image (List I) (List I) (Classical.decEq _) (List.drop h) S, matrixCutAmplitude S C h s * star (matrixCutAmplitude S C h s)

/-- Exact ordered pair expansion of the genuine finite suffix Gram. -/
theorem matrixCutGram_pairs (S : Finset (List I)) (C : List I → Matrix ν ν ℂ) (h : ℕ) :
    matrixCutGram S C h = ∑ u ∈ S, ∑ v ∈ S,
      if u.drop h = v.drop h then
        matrixWickTerm (C u) (u.take h) * star (matrixWickTerm (C v) (v.take h)) else 0 := by
  have hi (p : Prop) (d : Decidable p)
      (x y : CStarMatrix ν ν (WordSpace I →L[ℂ] WordSpace I)) :
      @ite _ p d x y = @ite _ p (Classical.propDecidable p) x y := by
    rw [Subsingleton.elim d (Classical.propDecidable p)]
  simp only [matrixCutGram, matrixCutAmplitude]
  simp_rw [hi]
  exact (finite_fiber_Gram S (List.drop h)
    (fun u => matrixWickTerm (C u) (u.take h))).symm

/-- Positivity in the full canonical matrix operator cone, for every prefix cut. -/
theorem matrixCutGram_nonneg (S : Finset (List I)) (C : List I → Matrix ν ν ℂ) (h : ℕ) :
    0 ≤ matrixCutGram S C h :=
  Finset.sum_nonneg (fun _ _ => mul_star_self_nonneg _)

/-- Literal homogeneous damped contraction polynomial with ordered matrix coefficients. -/
def matrixHomogeneousDampedProduct (S : Finset (List I)) (C : List I → Matrix ν ν ℂ)
    (α : ℂ) (n : ℕ) : CStarMatrix ν ν (WordSpace I →L[ℂ] WordSpace I) :=
  ∑ u ∈ S, ∑ v ∈ S, ∑ k ∈ Finset.range (n + 1), α ^ (2 * k) •
    (if u.drop k = v.drop k then
      matrixWickTerm (C u * (C v).conjTranspose) (u.take k ++ (v.take k).reverse) else 0)

/-- Exact finite homogeneous decomposition into actual positive suffix Grams.
The left side is a literal polynomial; the actual OU identification is separate. -/
theorem matrixHomogeneousDampedProduct_Gram (S : Finset (List I))
    (C : List I → Matrix ν ν ℂ) (n : ℕ) (hn : ∀ u ∈ S, u.length = n) (α : ℂ) :
    matrixHomogeneousDampedProduct S C α n =
      α ^ (2 * n) • matrixCutGram S C n +
      (1 - α ^ 2) • ∑ h ∈ Finset.range n, α ^ (2 * h) • matrixCutGram S C h := by
  have hp : ∀ u ∈ S, ∀ v ∈ S,
      (∑ k ∈ Finset.range (n + 1), α ^ (2 * k) •
        (if u.drop k = v.drop k then
          matrixWickTerm (C u * (C v).conjTranspose) (u.take k ++ (v.take k).reverse) else 0)) =
      α ^ (2 * n) • (matrixWickTerm (C u) u * star (matrixWickTerm (C v) v)) +
      (1 - α ^ 2) • ∑ h ∈ Finset.range n, α ^ (2 * h) •
        (if u.drop h = v.drop h then
          matrixWickTerm (C u) (u.take h) * star (matrixWickTerm (C v) (v.take h)) else 0) := by
    intro u hu v hv
    simpa only [hn u hu] using matrixWickTerm_damped_equalDegree_suffix_Gram
      (C u) (C v) u v ((hn u hu).trans (hn v hv).symm) α
  unfold matrixHomogeneousDampedProduct
  trans ∑ u ∈ S, ∑ v ∈ S,
    (α ^ (2 * n) • (matrixWickTerm (C u) u * star (matrixWickTerm (C v) v)) +
      (1 - α ^ 2) • ∑ h ∈ Finset.range n, α ^ (2 * h) •
        (if u.drop h = v.drop h then
          matrixWickTerm (C u) (u.take h) * star (matrixWickTerm (C v) (v.take h)) else 0))
  · apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    exact hp u hu v hv
  ·
    simp only [Finset.sum_add_distrib, ← Finset.smul_sum]
    congr 1
    · rw [matrixCutGram_pairs]
      congr 1
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      simp [List.drop_eq_nil_iff.mpr (hn u hu).le, List.drop_eq_nil_iff.mpr (hn v hv).le,
        List.take_of_length_le (hn u hu).le, List.take_of_length_le (hn v hv).le]
    · congr 1
      conv_lhs =>
        arg 2
        ext u
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h hh
      simp only [← Finset.smul_sum]
      rw [matrixCutGram_pairs]

/-- Canonical matrix positivity of the exact finite homogeneous damped polynomial. -/
theorem matrixHomogeneousDampedProduct_nonneg (S : Finset (List I))
    (C : List I → Matrix ν ν ℂ) (n : ℕ) (hn : ∀ u ∈ S, u.length = n)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    0 ≤ matrixHomogeneousDampedProduct S C (α : ℂ) n := by
  apply (hilbertMatrixStarAlgEquiv_nonneg_iff _).mp
  rw [matrixHomogeneousDampedProduct_Gram S C n hn]
  simp only [map_add, map_smul, map_sum]
  apply add_nonneg
  · apply smul_nonneg
    · exact pow_nonneg ((RCLike.ofReal_nonneg (K := ℂ)).mpr hα) _
    · exact hilbertMatrixStarAlgEquiv_nonneg _ (matrixCutGram_nonneg S C n)
  · apply smul_nonneg
    · have hs : α ^ 2 ≤ 1 := by nlinarith
      have hp := (RCLike.ofReal_nonneg (K := ℂ)).mpr (sub_nonneg.mpr hs)
      change 0 ≤ ((1 - α ^ 2 : ℝ) : ℂ) at hp
      simpa only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow] using hp
    · apply Finset.sum_nonneg
      intro h _
      apply smul_nonneg
      · exact pow_nonneg ((RCLike.ofReal_nonneg (K := ℂ)).mpr hα) _
      · exact hilbertMatrixStarAlgEquiv_nonneg _ (matrixCutGram_nonneg S C h)

end FreeProbability.Fock

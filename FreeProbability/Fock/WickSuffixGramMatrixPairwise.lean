import FreeProbability.Fock.WickSuffixGramPairwise

/-! # Actual homogeneous matrix-coefficient suffix identities -/
noncomputable section
open scoped Classical BigOperators
namespace FreeProbability.Fock
variable {I ν : Type*} [Fintype ν]

/-- Entrywise scalar matrix coefficients applied to an actual bounded operator. -/
def matrixCoefficientOperator (C : Matrix ν ν ℂ) :
    (WordSpace I →L[ℂ] WordSpace I) →ₗ[ℂ]
      CStarMatrix ν ν (WordSpace I →L[ℂ] WordSpace I) where
  toFun T := CStarMatrix.ofMatrix (fun i j => C i j • T)
  map_add' T S := by
    apply CStarMatrix.ofMatrix.symm.injective
    funext i j
    change C i j • (T + S) = C i j • T + C i j • S
    exact smul_add _ _ _
  map_smul' c T := by
    apply CStarMatrix.ofMatrix.symm.injective
    funext i j
    change C i j • (c • T) = c • (C i j • T)
    exact smul_comm _ _ _

omit [Fintype ν] in
@[simp] theorem matrixCoefficientOperator_wick (C : Matrix ν ν ℂ) (w : List I) :
    matrixCoefficientOperator C (wick w) = matrixWickTerm C w := rfl

/-- Exact two-coefficient product as the genuine ordered matrix coefficient map. -/
theorem matrixWickTerm_mul_star_coefficient (C D : Matrix ν ν ℂ) (u v : List I) :
    matrixWickTerm C u * star (matrixWickTerm D v) =
      matrixCoefficientOperator (C * D.conjTranspose) (wick u * star (wick v)) :=
  matrixWickTerm_mul_star C D u v

/-- The homogeneous pairwise suffix decomposition in the genuine matrix algebra.
Matrix coefficient order is preserved in every summand, for all complex parameters. -/
theorem matrixWickTerm_damped_equalDegree_suffix_Gram (C D : Matrix ν ν ℂ)
    (u v : List I) (hl : u.length = v.length) (α : ℂ) :
    (∑ k ∈ Finset.range (u.length + 1), α ^ (2 * k) •
      (if u.drop k = v.drop k then
        matrixWickTerm (C * D.conjTranspose) (u.take k ++ (v.take k).reverse) else 0)) =
      α ^ (2 * u.length) • (matrixWickTerm C u * star (matrixWickTerm D v)) +
      (1 - α ^ 2) • ∑ h ∈ Finset.range u.length, α ^ (2 * h) •
        (if u.drop h = v.drop h then
          matrixWickTerm C (u.take h) * star (matrixWickTerm D (v.take h)) else 0) := by
  have hh := congrArg (matrixCoefficientOperator (I := I) (C * D.conjTranspose))
    (wick_damped_equalDegree_suffix_Gram u v hl α)
  simp only [map_sum, map_smul, map_add, apply_ite, map_zero] at hh
  simpa only [← matrixWickTerm_mul_star_coefficient, matrixCoefficientOperator_wick,
    smul_ite] using hh

end FreeProbability.Fock

import FreeProbability.Fock.WickSuffixGramActualOUFinite

/-! # Actual common matrix vacuum marginals of finite suffix-cut Grams -/
noncomputable section
open scoped Classical BigOperators
namespace FreeProbability.Fock
variable {I ν : Type*} [Fintype ν]

/-- Genuine entrywise vacuum marginal, with its actual finite matrix codomain. -/
def matrixVacuumMarginal : CStarMatrix ν ν (WordSpace I →L[ℂ] WordSpace I) →ₗ[ℂ]
    Matrix ν ν ℂ :=
  (CStarMatrix.ofMatrixₗ (R := ℂ)).symm.toLinearMap.comp (CStarMatrix.mapₗ (vacuumLinear (I := I)))

/-- Wick orthogonality in the star-square orientation used by suffix Grams. -/
theorem vacuumExpectation_wick_mul_star (u v : List I) :
    vacuumExpectation (wick u * star (wick v)) = if u = v then 1 else 0 := by
  have hs : star (wick v) ∈ semicircularAlgebra I := star_mem (wick_mem_algebra v)
  rw [vacuumExpectation_mul_comm_on_semicircularAlgebra (wick_mem_algebra u) hs,
    vacuumExpectation_wick_star_mul]
  simp only [eq_comm]

/-- The exact ordered matrix marginal of two actual coefficient Wick terms. -/
theorem matrixVacuumMarginal_Wick_product (C D : Matrix ν ν ℂ) (u v : List I) :
    matrixVacuumMarginal (matrixWickTerm C u * star (matrixWickTerm D v)) =
      if u = v then C * D.conjTranspose else 0 := by
  rw [matrixWickTerm_mul_star]
  funext i j
  change vacuumExpectation ((C * D.conjTranspose) i j • (wick u * star (wick v))) = _
  have hm := map_smul (vacuumLinear (I := I)) ((C * D.conjTranspose) i j)
    (wick u * star (wick v))
  change vacuumExpectation ((C * D.conjTranspose) i j • (wick u * star (wick v))) =
    (C * D.conjTranspose) i j • vacuumExpectation (wick u * star (wick v)) at hm
  rw [hm, vacuumExpectation_wick_mul_star]
  by_cases h : u = v <;> simp [h]

/-- The finite coefficient covariance, allowing arbitrary singular marginals. -/
def matrixCoefficientMarginal (S : Finset (List I)) (C : List I → Matrix ν ν ℂ) :
    Matrix ν ν ℂ := ∑ w ∈ S, C w * (C w).conjTranspose

/-- Every actual suffix-cut Gram has the same genuine matrix vacuum marginal.
No degree restriction is needed for this orthogonality identity. -/
theorem matrixCutGram_vacuum_marginal (S : Finset (List I))
    (C : List I → Matrix ν ν ℂ) (h : ℕ) :
    matrixVacuumMarginal (matrixCutGram S C h) = matrixCoefficientMarginal S C := by
  rw [matrixCutGram_pairs, map_sum]
  unfold matrixCoefficientMarginal
  apply Finset.sum_congr rfl
  intro u hu
  rw [map_sum]
  have ht : ∀ v ∈ S,
      matrixVacuumMarginal
        (if u.drop h = v.drop h then
          matrixWickTerm (C u) (u.take h) * star (matrixWickTerm (C v) (v.take h)) else 0) =
        if u = v then C u * (C v).conjTranspose else 0 := by
    intro v _
    by_cases hs : u.drop h = v.drop h
    · simp only [hs, ite_true, matrixVacuumMarginal_Wick_product]
      have he : u.take h = v.take h ↔ u = v := by
        constructor
        · intro hp
          rw [← List.take_append_drop h u, ← List.take_append_drop h v, hp, hs]
        · intro hp
          subst v
          rfl
      simp only [he]
    · have huv : u ≠ v := fun he => hs (congrArg (List.drop h) he)
      simp only [hs, ite_false, map_zero, huv]
  calc
    _ = ∑ v ∈ S, if u = v then C u * (C v).conjTranspose else 0 :=
      Finset.sum_congr rfl ht
    _ = C u * (C u).conjTranspose := by simp [hu]

end FreeProbability.Fock

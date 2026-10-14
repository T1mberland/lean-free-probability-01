import FreeProbability.Fock.WickSuffixGramOrderScalar

/-! # Genuine full-matrix order bound for each finite-alphabet suffix fiber -/
noncomputable section
open scoped Classical BigOperators ComplexOrder
namespace FreeProbability.Fock
variable {I ν : Type*} [Fintype I] [Fintype ν]

/-- Each actual suffix amplitude square has the complete matrix coefficient bound. -/
theorem matrixCutAmplitude_mul_star_le (S : Finset (List I))
    (C : List I → Matrix ν ν ℂ) (h : ℕ) (s : List I)
    (hl : ∀ u ∈ S, h ≤ u.length) :
    matrixCutAmplitude S C h s * star (matrixCutAmplitude S C h s) ≤
      (((((Fintype.card I) ^ h : ℕ) : ℝ) * ((h : ℝ) + 1) ^ 2 : ℝ) : ℂ) •
        matrixScalarEmbed (I := I)
          (matrixCoefficientMarginal (S.filter (fun u => u.drop h = s)) C) := by
  let F := S.filter (fun u => u.drop h = s)
  let A := fun u => matrixWickTerm (C u) (u.take h)
  have hB : matrixCutAmplitude S C h s = ∑ u ∈ F, A u := by
    simp only [matrixCutAmplitude, F, A, Finset.sum_filter]
  have hs : (∑ u ∈ F, A u * star (A u)) ≤
      ((((h : ℝ) + 1) ^ 2 : ℝ) : ℂ) • ∑ u ∈ F,
        matrixScalarEmbed (I := I) (C u * (C u).conjTranspose) := by
    calc
      _ ≤ ∑ u ∈ F, ((((h : ℝ) + 1) ^ 2 : ℝ) : ℂ) •
          matrixScalarEmbed (I := I) (C u * (C u).conjTranspose) := by
        apply Finset.sum_le_sum
        intro u hu
        have hh : (u.take h).length = h := by
          simp [List.length_take, Nat.min_eq_left (hl u (Finset.mem_filter.mp hu).1)]
        simpa only [A, hh] using matrixWickTerm_mul_star_le (C u) (u.take h)
      _ = _ := Finset.smul_sum.symm
  have hn : 0 ≤ ∑ u ∈ F, A u * star (A u) :=
    Finset.sum_nonneg (fun _ _ => mul_star_self_nonneg _)
  have hcard : (F.card : ℝ) ≤ (((Fintype.card I) ^ h : ℕ) : ℝ) := by
    exact_mod_cast suffixFiber_card_le S h s hl
  have hc := matrixOperator_smul_scalar_mono (F.card : ℝ)
    (((Fintype.card I) ^ h : ℕ) : ℝ) hcard _ hn
  have hm := matrixOperator_smul_mono (((Fintype.card I) ^ h : ℕ) : ℝ)
    (Nat.cast_nonneg _) hs
  rw [hB]
  calc
    _ ≤ (F.card : ℂ) • ∑ u ∈ F, A u * star (A u) := finiteMatrixOperatorGram_le F A
    _ ≤ (((Fintype.card I) ^ h : ℕ) : ℂ) • ∑ u ∈ F, A u * star (A u) := by
      simpa only [Complex.ofReal_natCast] using hc
    _ ≤ (((Fintype.card I) ^ h : ℕ) : ℂ) •
        (((((h : ℝ) + 1) ^ 2 : ℝ) : ℂ) • ∑ u ∈ F,
          matrixScalarEmbed (I := I) (C u * (C u).conjTranspose)) := by
      simpa only [Complex.ofReal_natCast] using hm
    _ = _ := by
      simp only [smul_smul, Complex.ofReal_mul, Complex.ofReal_natCast]
      congr 1
      change (∑ u ∈ F, matrixScalarEmbed (I := I) (C u * (C u).conjTranspose)) = _
      simp only [← matrixScalarEmbedLinear_apply, ← map_sum, matrixCoefficientMarginal]
      rfl

end FreeProbability.Fock

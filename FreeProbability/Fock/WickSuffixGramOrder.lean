import FreeProbability.Fock.WickSuffixGramOrderFiber

/-! # Full canonical matrix order bound for finite-alphabet suffix Grams -/
noncomputable section
open scoped Classical BigOperators
namespace FreeProbability.Fock
variable {I ν : Type*} [Fintype I] [Fintype ν]

omit [Fintype I] in
/-- Exact finite coefficient partition by terminal cuts. -/
theorem matrixCoefficientMarginal_fibers (S : Finset (List I))
    (C : List I → Matrix ν ν ℂ) (h : ℕ) :
    (∑ s ∈ @Finset.image (List I) (List I) (Classical.decEq _) (List.drop h) S,
      matrixCoefficientMarginal (S.filter (fun u => u.drop h = s)) C) =
        matrixCoefficientMarginal S C := by
  unfold matrixCoefficientMarginal
  apply Finset.sum_fiberwise_of_maps_to
  intro u hu
  let : DecidableEq (List I) := Classical.decEq _
  exact Finset.mem_image.mpr ⟨u, hu, rfl⟩

/-- Genuine canonical matrix inequality, including empty alphabets and singular marginals. -/
theorem matrixCutGram_le (S : Finset (List I)) (C : List I → Matrix ν ν ℂ) (h : ℕ)
    (hl : ∀ u ∈ S, h ≤ u.length) :
    matrixCutGram S C h ≤
      (((((Fintype.card I) ^ h : ℕ) : ℝ) * ((h : ℝ) + 1) ^ 2 : ℝ) : ℂ) •
        matrixScalarEmbed (I := I) (matrixCoefficientMarginal S C) := by
  unfold matrixCutGram
  calc
    _ ≤ ∑ s ∈ @Finset.image (List I) (List I) (Classical.decEq _) (List.drop h) S,
        (((((Fintype.card I) ^ h : ℕ) : ℝ) * ((h : ℝ) + 1) ^ 2 : ℝ) : ℂ) •
          matrixScalarEmbed (I := I)
            (matrixCoefficientMarginal (S.filter (fun u => u.drop h = s)) C) :=
      Finset.sum_le_sum (fun s _ => matrixCutAmplitude_mul_star_le S C h s hl)
    _ = _ := by
      rw [← Finset.smul_sum]
      congr 1
      simp only [← matrixScalarEmbedLinear_apply, ← map_sum]
      rw [matrixCoefficientMarginal_fibers]

/-- The homogeneous common-marginal bound at every residual prefix degree. -/
theorem matrixCutGram_le_homogeneous (S : Finset (List I)) (C : List I → Matrix ν ν ℂ)
    (n h : ℕ) (hn : ∀ u ∈ S, u.length = n) (hh : h ≤ n) :
    matrixCutGram S C h ≤
      (((((Fintype.card I) ^ h : ℕ) : ℝ) * ((h : ℝ) + 1) ^ 2 : ℝ) : ℂ) •
        matrixScalarEmbed (I := I) (matrixCoefficientMarginal S C) :=
  matrixCutGram_le S C h (fun u hu => by rw [hn u hu]; exact hh)

end FreeProbability.Fock

import FreeProbability.Fock.WickSuffixGramMatrixPairwise

/-! # Finite ordered Gram regrouping along actual suffix fibers -/
noncomputable section
open scoped Classical BigOperators
namespace FreeProbability.Fock

/-- Exact finite fiber grouping, preserving the order of noncommuting factors.
This algebraic identity applies in particular to the actual operator matrix algebra. -/
theorem finite_fiber_Gram {ι σ A : Type*} [NonUnitalRing A] [StarRing A]
    (S : Finset ι) (p : ι → σ) (a : ι → A) :
    (∑ u ∈ S, ∑ v ∈ S, if p u = p v then a u * star (a v) else 0) =
      ∑ s ∈ S.image p,
        (∑ u ∈ S, if p u = s then a u else 0) *
          star (∑ v ∈ S, if p v = s then a v else 0) := by
  have he (s : σ) :
      (∑ u ∈ S, if p u = s then a u else 0) *
          star (∑ v ∈ S, if p v = s then a v else 0) =
        ∑ u ∈ S, ∑ v ∈ S,
          if p u = s ∧ p v = s then a u * star (a v) else 0 := by
    rw [star_sum, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    by_cases hu : p u = s <;> by_cases hv : p v = s <;> simp [hu, hv]
  symm
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_eq_single (p u)]
  · by_cases h : p u = p v <;> simp [h, eq_comm]
  · intro s _ hs
    have hn : p u ≠ s := Ne.symm hs
    simp [hn]
  · intro hn
    exact (hn (Finset.mem_image.mpr ⟨u, hu, rfl⟩)).elim

end FreeProbability.Fock

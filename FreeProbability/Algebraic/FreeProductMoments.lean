import FreeProbability.Algebraic.KrewerasMultiplicativeMoments
import FreeProbability.Combinatorics.OrderedPairProducts

/-! # Kreweras formulas for actual ordered products of free variables -/

namespace FreeProbability

open NoncrossingPartition

variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]

/-- The moment of actual coordinatewise products of two free tuples is the
Kreweras cumulant–moment sum. No trace assumption or commutation is needed. -/
theorem FreelyIndependent.expectation_prod_eq_kreweras_sum {φ : ProbabilitySpace 𝕜 A}
    {B : Fin 2 → Subalgebra 𝕜 A} (hfree : FreelyIndependent φ B) {n : ℕ}
    (a b : Fin n → A) (ha : ∀ i, a i ∈ B 0) (hb : ∀ i, b i ∈ B 1) :
    φ.expectation (List.ofFn (fun i => a i * b i)).prod =
      ∑ p : NoncrossingPartition n,
        orderedPartitionContribution (cumulant φ) a p *
          orderedPartitionContribution (fun w => φ.expectation w.prod) b p.kreweras := by
  classical
  have hmem : ∀ i, interleavedWord a b i ∈ B (parityLabel i) := by
    intro i
    by_cases hi : i.val % 2 = 0
    · have hl : parityLabel i = 0 := by
        apply Fin.ext
        exact hi
      rw [hl]
      simpa only [interleavedWord, hi, ite_true] using ha (halfPosition i)
    · have hl : parityLabel i = 1 := by
        apply Fin.ext
        change i.val % 2 = 1
        omega
      rw [hl]
      simpa only [interleavedWord, hi, ite_false] using hb (halfPosition i)
  have h := hfree.expectation_eq_kreweras_sum (interleavedWord a b) hmem
  have ho : interleavedWord a b ∘ oddOrderEmbedding = a := by
    funext i
    exact interleavedWord_odd a b i
  have he : interleavedWord a b ∘ evenOrderEmbedding = b := by
    funext i
    exact interleavedWord_even a b i
  rw [ho, he, prod_ofFn_pairs] at h
  simpa only [interleavedWord_odd, interleavedWord_even] using h

/-- All powers of an actual product of two free variables satisfy the Kreweras
moment identity, including order zero. -/
theorem FreelyIndependent.expectation_pow_mul_eq_kreweras_sum {φ : ProbabilitySpace 𝕜 A}
    {B : Fin 2 → Subalgebra 𝕜 A} (hfree : FreelyIndependent φ B)
    (a b : A) (ha : a ∈ B 0) (hb : b ∈ B 1) (n : ℕ) :
    φ.expectation ((a * b) ^ n) =
      ∑ p : NoncrossingPartition n,
        orderedPartitionContribution (cumulant φ) (fun _ => a) p *
          orderedPartitionContribution (fun w => φ.expectation w.prod) (fun _ => b) p.kreweras := by
  simpa only [List.ofFn_const, List.prod_replicate] using
    hfree.expectation_prod_eq_kreweras_sum (fun _ : Fin n => a) (fun _ => b)
      (fun _ => ha) (fun _ => hb)

end FreeProbability

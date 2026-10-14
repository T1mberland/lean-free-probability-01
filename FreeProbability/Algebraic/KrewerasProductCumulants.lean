import FreeProbability.Algebraic.FreeProductMoments
import FreeProbability.Algebraic.CumulantIntervalProducts
import FreeProbability.Combinatorics.NoncrossingKrewerasTopFiber

/-!
# Boxed cumulants of actual free products

The cumulant of a nonempty tuple of coordinatewise products of two free tuples
is the sum of products of the marginal partition cumulants over `p` and its
actual Kreweras complement. Compatibility, the top fiber, block counts, and
raw incidence connectivity are all proved prerequisites.
-/

namespace FreeProbability

open NoncrossingPartition

variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]

/-- The actual boxed product-cumulant identity on a nonempty alternating tuple. -/
theorem FreelyIndependent.cumulant_pairs_eq_kreweras_sum {φ : ProbabilitySpace 𝕜 A}
    {B : Fin 2 → Subalgebra 𝕜 A} (hfree : FreelyIndependent φ B) {n : ℕ}
    (x : Fin (2 * n) → A) (hmem : ∀ a, x a ∈ B (parityLabel a)) (hn : 0 < n) :
    cumulant φ (List.ofFn (fun a => x (oddPosition a) * x (evenPosition a))) =
      ∑ p : NoncrossingPartition n,
        orderedPartitionContribution (cumulant φ) (x ∘ oddOrderEmbedding) p *
          orderedPartitionContribution (cumulant φ) (x ∘ evenOrderEmbedding) p.kreweras := by
  classical
  rw [← intervalProducts_halfPosition, cumulant_intervalProducts_top φ halfPosition
    halfPosition_monotone halfPosition_surjective x hn]
  let f : NoncrossingPartition n → IntervalProductTopFiber halfPosition halfPosition_monotone := fun p =>
    ⟨p.interleave p.kreweras le_rfl, (p.interleave_sup_pairInterval_eq_top_iff p.kreweras le_rfl).mpr rfl⟩
  have hf : Function.Injective f := by
    intro p q hpq
    have he := congrArg (fun r : IntervalProductTopFiber halfPosition halfPosition_monotone =>
      r.val.restrict oddOrderEmbedding) hpq
    simpa only [f, restrict_interleave_odd] using he
  have hz (r : IntervalProductTopFiber halfPosition halfPosition_monotone)
      (hr : ¬ ∃ p, f p = r) : orderedPartitionContribution (cumulant φ) x r.val = 0 := by
    have hnot : ¬ r.val.ParityPreserving := by
      intro hpar
      let p := r.val.restrict oddOrderEmbedding
      let q := r.val.restrict evenOrderEmbedding
      have hq : q ≤ p.kreweras := r.val.restrict_even_le_kreweras hpar
      have he : p.interleave q hq = r.val := r.val.interleave_restrict hpar
      have ht : p.interleave q hq ⊔ pairIntervalPartition n = ⊤ := by
        rw [he]
        exact r.property
      have hqe : q = p.kreweras := (p.interleave_sup_pairInterval_eq_top_iff q hq).mp ht
      apply hr
      refine ⟨p, Subtype.ext ?_⟩
      change p.interleave p.kreweras le_rfl = r.val
      calc
        _ = p.interleave q hq := by
          apply Subtype.ext
          change interleaveSetoid p p.kreweras = interleaveSetoid p q
          rw [hqe]
        _ = r.val := he
    unfold ParityPreserving at hnot
    push Not at hnot
    obtain ⟨a, b, hab, hneq⟩ := hnot
    apply hfree.orderedContribution_eq_zero_of_mixed x parityLabel hmem r.val
    exact ⟨a, b, hab, fun h => hneq (congrArg Fin.val h)⟩
  symm
  apply Fintype.sum_of_injective f
  · exact hf
  · exact hz
  · intro p
    exact (orderedPartitionContribution_interleave (cumulant φ) x p p.kreweras le_rfl).symm

/-- Boxed convolution holds for the cumulants of actual coordinatewise products
of two freely independent tuples, without traciality or commutation assumptions. -/
theorem FreelyIndependent.cumulant_prod_eq_kreweras_sum {φ : ProbabilitySpace 𝕜 A}
    {B : Fin 2 → Subalgebra 𝕜 A} (hfree : FreelyIndependent φ B) {n : ℕ}
    (a b : Fin n → A) (ha : ∀ i, a i ∈ B 0) (hb : ∀ i, b i ∈ B 1) (hn : 0 < n) :
    cumulant φ (List.ofFn (fun i => a i * b i)) =
      ∑ p : NoncrossingPartition n,
        orderedPartitionContribution (cumulant φ) a p *
          orderedPartitionContribution (cumulant φ) b p.kreweras := by
  have hmem : ∀ i, interleavedWord a b i ∈ B (parityLabel i) := by
    intro i
    by_cases hi : i.val % 2 = 0
    · have hl : parityLabel i = 0 := Fin.ext hi
      rw [hl]
      simpa only [interleavedWord, hi, ite_true] using ha (halfPosition i)
    · have hl : parityLabel i = 1 := by
        apply Fin.ext
        change i.val % 2 = 1
        omega
      rw [hl]
      simpa only [interleavedWord, hi, ite_false] using hb (halfPosition i)
  have h := hfree.cumulant_pairs_eq_kreweras_sum (interleavedWord a b) hmem hn
  have ho : interleavedWord a b ∘ oddOrderEmbedding = a := funext (interleavedWord_odd a b)
  have he : interleavedWord a b ∘ evenOrderEmbedding = b := funext (interleavedWord_even a b)
  rw [ho, he] at h
  simpa only [interleavedWord_odd, interleavedWord_even] using h

/-- Every positive-order cumulant of an actual product is its marginal boxed
Kreweras convolution coefficient. -/
theorem FreelyIndependent.cumulant_replicate_mul_eq_kreweras_sum {φ : ProbabilitySpace 𝕜 A}
    {B : Fin 2 → Subalgebra 𝕜 A} (hfree : FreelyIndependent φ B)
    (a b : A) (ha : a ∈ B 0) (hb : b ∈ B 1) (n : ℕ) (hn : 0 < n) :
    cumulant φ (List.replicate n (a * b)) =
      ∑ p : NoncrossingPartition n,
        orderedPartitionContribution (cumulant φ) (fun _ => a) p *
          orderedPartitionContribution (cumulant φ) (fun _ => b) p.kreweras := by
  simpa only [List.ofFn_const] using hfree.cumulant_prod_eq_kreweras_sum
    (fun _ : Fin n => a) (fun _ => b) (fun _ => ha) (fun _ => hb) hn

end FreeProbability

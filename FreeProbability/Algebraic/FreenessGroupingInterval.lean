import FreeProbability.Algebraic.CumulantMonochromatic
import FreeProbability.Algebraic.CumulantConsecutiveProducts
import FreeProbability.Algebraic.CumulantIntervalProducts
import FreeProbability.Combinatorics.NoncrossingIntervalJoin

/-! # Interval-product cumulants for arbitrary grouping of free labels -/

noncomputable section
namespace FreeProbability

/-- A top interval-join fiber whose blocks preserve a grouped label forces
all final group labels to coincide. The raw join introduces no crossings. -/
theorem grouped_labels_constant_of_interval_top_join {n m : ℕ} {J : Type*}
    (t : ConsecutiveFusion n m) (p : NoncrossingPartition n) (label : Fin m → J)
    (hjoin : p ⊔ t.intervalPartition = ⊤)
    (hmono : ∀ a b, p.val.r a b → label (t.quotient a) = label (t.quotient b)) :
    ∀ a b, label a = label b := by
  let K := Setoid.ker (label ∘ t.quotient)
  have hp : p.val ≤ K := hmono
  have hσ : t.intervalPartition.val ≤ K := by
    intro a b hab
    exact congrArg label ((t.intervalPartition_rel a b).mp hab)
  have hle : (p ⊔ t.intervalPartition).val ≤ K := by
    rw [t.sup_intervalPartition_val]
    exact sup_le hp hσ
  rw [hjoin] at hle
  intro a b
  obtain ⟨u, hu⟩ := t.quotient_surjective a
  obtain ⟨v, hv⟩ := t.quotient_surjective b
  have h := hle (show (⊤ : NoncrossingPartition n).val.r u v from by rw [NoncrossingPartition.top_eq_indiscrete]; trivial)
  change label (t.quotient u) = label (t.quotient v) at h
  simpa only [hu, hv] using h

variable {𝕜 A I J : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]

/-- Consecutive products of original free letters have zero cumulant whenever
their arbitrary grouped labels are mixed. No cardinality assumption on the
original or grouped index types is imposed. -/
theorem FreelyIndependent.cumulant_consecutiveProducts_eq_zero_of_grouped_mixed
    {φ : ProbabilitySpace 𝕜 A} {B : I → Subalgebra 𝕜 A} (hf : FreelyIndependent φ B)
    (g : I → J) {n m : ℕ} (t : ConsecutiveFusion n m) (x : Fin n → A)
    (color : Fin n → I) (label : Fin m → J) (hmem : ∀ a, x a ∈ B (color a))
    (hgroup : ∀ a, g (color a) = label (t.quotient a))
    (hmixed : ∃ a b, label a ≠ label b) :
    cumulant φ (List.ofFn (t.applyWord x)) = 0 := by
  obtain ⟨a, b, hab⟩ := hmixed
  have hm : 0 < m := by have h := a.isLt; omega
  rw [cumulant_consecutiveProducts φ t x hm]
  apply Finset.sum_eq_zero
  intro p _
  apply hf.orderedContribution_eq_zero_of_mixed x color hmem p.val
  by_contra hmix
  have hmono : ∀ u v, p.val.val.r u v → label (t.quotient u) = label (t.quotient v) := by
    intro u v huv
    have hcolor : color u = color v := by
      by_contra hneq
      exact hmix ⟨u, v, huv, hneq⟩
    rw [← hgroup u, ← hgroup v, hcolor]
  have hjoin : p.val ⊔ t.intervalPartition = ⊤ := by
    simpa only [t.expand_top] using p.property
  exact hab (grouped_labels_constant_of_interval_top_join t p.val label hjoin hmono a b)
/-- The grouping result for an independently supplied monotone surjective
quotient: its actual ordered fiber products have zero mixed group cumulant. -/
theorem FreelyIndependent.cumulant_intervalProducts_eq_zero_of_grouped_mixed
    {φ : ProbabilitySpace 𝕜 A} {B : I → Subalgebra 𝕜 A} (hf : FreelyIndependent φ B)
    (g : I → J) {n m : ℕ} (f : Fin n → Fin m) (hmono : Monotone f)
    (hs : Function.Surjective f) (x : Fin n → A) (color : Fin n → I)
    (label : Fin m → J) (hmem : ∀ a, x a ∈ B (color a))
    (hgroup : ∀ a, g (color a) = label (f a))
    (hmixed : ∃ a b, label a ≠ label b) :
    cumulant φ (List.ofFn (intervalProducts f x)) = 0 := by
  obtain ⟨t, ht⟩ := ConsecutiveFusion.exists_quotient_eq f hmono hs
  have hword : t.applyWord x = intervalProducts f x := by
    rw [t.applyWord_eq_intervalProducts, ht]
  rw [← hword]
  exact hf.cumulant_consecutiveProducts_eq_zero_of_grouped_mixed g t x color label hmem
    (fun a => by rw [ht]; exact hgroup a) hmixed
end FreeProbability

import FreeProbability.Algebraic.CumulantConsecutiveProducts
import FreeProbability.Combinatorics.ConsecutiveFusionWord

/-!
# The general cumulant formula for supplied interval groupings

The grouping is any monotone surjection `f : Fin n → Fin m`. Each argument on
the left is the actual sorted product over the corresponding nonempty interval
fiber of `f`; no fusion plan occurs in the public statement.
-/

namespace FreeProbability

/-- Pullback of a partition through a monotone word quotient. -/
def intervalPartitionPullback {n m : ℕ} (f : Fin n → Fin m) (hf : Monotone f)
    (q : NoncrossingPartition m) : NoncrossingPartition n :=
  ⟨Setoid.comap f q.val, q.property.comap_monotone f hf⟩

/-- The actual interval partition consisting of the quotient fibers. -/
def quotientIntervalPartition {n m : ℕ} (f : Fin n → Fin m) (hf : Monotone f) :
    NoncrossingPartition n := intervalPartitionPullback f hf (NoncrossingPartition.discrete m)

/-- Partitions whose join with the grouping interval partition is a supplied
final partition pulled back to the original positions. -/
abbrev IntervalProductFiber {n m : ℕ} (f : Fin n → Fin m) (hf : Monotone f)
    (q : NoncrossingPartition m) :=
  {p : NoncrossingPartition n // p ⊔ quotientIntervalPartition f hf = intervalPartitionPullback f hf q}

noncomputable instance intervalProductFiberFintype {n m : ℕ} (f : Fin n → Fin m)
    (hf : Monotone f) (q : NoncrossingPartition m) : Fintype (IntervalProductFiber f hf q) :=
  Fintype.ofFinite _

private theorem pullback_eq_expand {n m : ℕ} (t : ConsecutiveFusion n m)
    (f : Fin n → Fin m) (hf : Monotone f) (ht : t.quotient = f) (q : NoncrossingPartition m) :
    intervalPartitionPullback f hf q = t.expand q := by
  apply Subtype.ext
  apply Setoid.ext
  intro a b
  rw [t.expand_rel]
  change q.val.r (f a) (f b) ↔ q.val.r (t.quotient a) (t.quotient b)
  rw [ht]

/-- At every final partition, interval-product cumulants are exactly the
original cumulant contributions in the corresponding interval-join fiber. -/
theorem orderedCumulantContribution_intervalProducts {𝕜 A : Type*} [Field 𝕜] [Ring A]
    [Algebra 𝕜 A] (φ : ProbabilitySpace 𝕜 A) {n m : ℕ} (f : Fin n → Fin m)
    (hf : Monotone f) (hs : Function.Surjective f) (x : Fin n → A) (q : NoncrossingPartition m) :
    orderedPartitionContribution (cumulant φ) (intervalProducts f x) q =
      ∑ p : IntervalProductFiber f hf q, orderedPartitionContribution (cumulant φ) x p.val := by
  classical
  obtain ⟨t, ht⟩ := ConsecutiveFusion.exists_quotient_eq f hf hs
  have hw : t.applyWord x = intervalProducts f x := by rw [t.applyWord_eq_intervalProducts, ht]
  rw [← hw, orderedCumulantContribution_consecutiveProducts_join]
  have hk : quotientIntervalPartition f hf = t.intervalPartition :=
    pullback_eq_expand t f hf ht _
  have hq := pullback_eq_expand t f hf ht q
  let e : t.JoinFiber q ≃ IntervalProductFiber f hf q :=
    { toFun := fun p => ⟨p.val, by simpa only [hk, hq] using p.property⟩
      invFun := fun p => ⟨p.val, by simpa only [hk, hq] using p.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

/-- The general product-cumulant identity for independently supplied nonempty
consecutive interval groups in an arbitrary algebraic probability space. -/
theorem cumulant_intervalProducts {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
    (φ : ProbabilitySpace 𝕜 A) {n m : ℕ} (f : Fin n → Fin m) (hf : Monotone f)
    (hs : Function.Surjective f) (x : Fin n → A) (hm : 0 < m) :
    cumulant φ (List.ofFn (intervalProducts f x)) =
      ∑ p : IntervalProductFiber f hf (⊤ : NoncrossingPartition m),
        orderedPartitionContribution (cumulant φ) x p.val := by
  rw [← orderedCumulantContribution_intervalProducts φ f hf hs x,
    NoncrossingPartition.top_eq_indiscrete]
  exact (orderedPartitionContribution_indiscrete φ _ hm).symm

/-- The standard top join fiber for a supplied interval grouping. -/
abbrev IntervalProductTopFiber {n m : ℕ} (f : Fin n → Fin m) (hf : Monotone f) :=
  {p : NoncrossingPartition n // p ⊔ quotientIntervalPartition f hf = ⊤}

noncomputable instance intervalProductTopFiberFintype {n m : ℕ} (f : Fin n → Fin m)
    (hf : Monotone f) : Fintype (IntervalProductTopFiber f hf) := Fintype.ofFinite _

/-- The usual product-cumulant formula with its literal top join condition. -/
theorem cumulant_intervalProducts_top {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
    (φ : ProbabilitySpace 𝕜 A) {n m : ℕ} (f : Fin n → Fin m) (hf : Monotone f)
    (hs : Function.Surjective f) (x : Fin n → A) (hm : 0 < m) :
    cumulant φ (List.ofFn (intervalProducts f x)) =
      ∑ p : IntervalProductTopFiber f hf,
        orderedPartitionContribution (cumulant φ) x p.val := by
  classical
  have htop : intervalPartitionPullback f hf (⊤ : NoncrossingPartition m) = ⊤ := by
    obtain ⟨t, ht⟩ := ConsecutiveFusion.exists_quotient_eq f hf hs
    rw [pullback_eq_expand t f hf ht, t.expand_top]
  rw [cumulant_intervalProducts φ f hf hs x hm]
  let e : IntervalProductFiber f hf (⊤ : NoncrossingPartition m) ≃ IntervalProductTopFiber f hf :=
    { toFun := fun p => ⟨p.val, by simpa only [htop] using p.property⟩
      invFun := fun p => ⟨p.val, by simpa only [htop] using p.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

end FreeProbability

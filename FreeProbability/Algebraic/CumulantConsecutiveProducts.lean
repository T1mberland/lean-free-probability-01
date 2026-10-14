import FreeProbability.Algebraic.CumulantAdjacentPartition
import FreeProbability.Combinatorics.ConsecutiveFusion

/-!
# Cumulants of consecutive interval products

For any finite sequence of adjacent word multiplications, the contribution of
any final noncrossing partition is the sum of original contributions in its
quotient fiber. These fibers are equivalently joins with the plan's genuine
consecutive interval partition. The top case is the usual product-cumulant
formula, with no commutativity hypothesis on the random variables.
-/

namespace FreeProbability

namespace ConsecutiveFusion

variable {n m : ℕ}

/-- The finite original-partition fiber of an interval fusion. -/
abbrev Fiber (t : ConsecutiveFusion n m) (q : NoncrossingPartition m) :=
  {p : NoncrossingPartition n // t.contract p = q}

noncomputable instance (t : ConsecutiveFusion n m) (q : NoncrossingPartition m) :
    Fintype (t.Fiber q) := Fintype.ofFinite _

/-- Regrouping two successive quotient fibers introduces no extra partitions. -/
noncomputable def fiberConsEquiv (i : Fin n) (t : ConsecutiveFusion n m) (q : NoncrossingPartition m) :
    (Σ r : t.Fiber q, {p : NoncrossingPartition (n + 1) // p.contract i = r.val}) ≃
      (ConsecutiveFusion.cons i t).Fiber q where
  toFun z := ⟨z.2.val, by simpa only [contract, z.2.property] using z.1.property⟩
  invFun p := ⟨⟨p.val.contract i, p.property⟩, ⟨p.val, rfl⟩⟩
  left_inv z := by
    rcases z with ⟨⟨r, hr⟩, ⟨p, hp⟩⟩
    cases hp
    rfl
  right_inv p := by cases p; rfl

end ConsecutiveFusion

variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A] {n m : ℕ}

/-- The exact all-partition cumulant formula for any sequence of consecutive
interval multiplications. -/
theorem orderedCumulantContribution_consecutiveProducts (φ : ProbabilitySpace 𝕜 A)
    (t : ConsecutiveFusion n m) (x : Fin n → A) (q : NoncrossingPartition m) :
    orderedPartitionContribution (cumulant φ) (t.applyWord x) q =
      ∑ p : t.Fiber q, orderedPartitionContribution (cumulant φ) x p.val := by
  classical
  induction t with
  | refl n =>
    have he : (ConsecutiveFusion.refl n).Fiber q ≃ Unit :=
      { toFun := fun _ => ()
        invFun := fun _ => ⟨q, rfl⟩
        left_inv := fun p => Subtype.ext p.property.symm
        right_inv := fun _ => rfl }
    symm
    calc
      _ = ∑ _ : Unit, orderedPartitionContribution (cumulant φ) x q :=
        Fintype.sum_equiv he _ _ (fun p => congrArg (orderedPartitionContribution (cumulant φ) x) p.property)
      _ = _ := by simp [ConsecutiveFusion.applyWord]
  | cons i t ih =>
    change orderedPartitionContribution (cumulant φ) (t.applyWord (fuseAdjacent x i)) q = _
    rw [ih]
    simp_rw [orderedCumulantContribution_fuseAdjacent_contract]
    trans ∑ z : (Σ r : t.Fiber q, {p : NoncrossingPartition (_ + 1) // p.contract i = r.val}),
      orderedPartitionContribution (cumulant φ) x z.2.val
    · exact (Fintype.sum_sigma (fun z : (Σ r : t.Fiber q, {p : NoncrossingPartition (_ + 1) // p.contract i = r.val}) => orderedPartitionContribution (cumulant φ) x z.2.val)).symm
    exact Fintype.sum_equiv (ConsecutiveFusion.fiberConsEquiv i t q) _ _ (fun _ => rfl)

/-- The noncrossing interval-join fiber of a consecutive fusion. -/
abbrev ConsecutiveFusion.JoinFiber (t : ConsecutiveFusion n m) (q : NoncrossingPartition m) :=
  {p : NoncrossingPartition n // p ⊔ t.intervalPartition = t.expand q}

noncomputable instance consecutiveJoinFiberFintype (t : ConsecutiveFusion n m)
    (q : NoncrossingPartition m) : Fintype (t.JoinFiber q) := Fintype.ofFinite _

/-- Interval joins give exactly the same quotient fiber. -/
def ConsecutiveFusion.joinFiberEquiv (t : ConsecutiveFusion n m) (q : NoncrossingPartition m) :
    t.Fiber q ≃ t.JoinFiber q where
  toFun p := ⟨p.val, (t.contract_eq_iff p.val q).mp p.property⟩
  invFun p := ⟨p.val, (t.contract_eq_iff p.val q).mpr p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The all-partition interval-product formula in its standard join-fiber form. -/
theorem orderedCumulantContribution_consecutiveProducts_join (φ : ProbabilitySpace 𝕜 A)
    (t : ConsecutiveFusion n m) (x : Fin n → A) (q : NoncrossingPartition m) :
    orderedPartitionContribution (cumulant φ) (t.applyWord x) q =
      ∑ p : t.JoinFiber q, orderedPartitionContribution (cumulant φ) x p.val := by
  rw [orderedCumulantContribution_consecutiveProducts]
  exact Fintype.sum_equiv (t.joinFiberEquiv q) _ _ (fun _ => rfl)

/-- The cumulant of any nonempty tuple of consecutive interval products equals
exactly the original partition contributions whose join with the interval
partition is top. -/
theorem cumulant_consecutiveProducts (φ : ProbabilitySpace 𝕜 A)
    (t : ConsecutiveFusion n m) (x : Fin n → A) (hm : 0 < m) :
    cumulant φ (List.ofFn (t.applyWord x)) =
      ∑ p : t.JoinFiber (⊤ : NoncrossingPartition m),
        orderedPartitionContribution (cumulant φ) x p.val := by
  rw [← orderedCumulantContribution_consecutiveProducts_join,
    NoncrossingPartition.top_eq_indiscrete]
  exact (orderedPartitionContribution_indiscrete φ _ hm).symm

end FreeProbability

import FreeProbability.RandomMatrix.OrthogonalWeingarten

/-! # Genuine loop bounds for joins of ordinary pairings -/

noncomputable section
open scoped Classical
namespace FreeProbability.Orthogonal

/-- The actual number of classes in the ordinary pairing join. -/
def pairingLoopCount {r : ℕ} (p q : OrdinaryPairing r) : ℕ :=
  Fintype.card (Quotient (pairingSetoid p.out ⊔ pairingSetoid q.out))

private theorem quotient_map_surjective {k : ℕ} (s t : Setoid (Fin k)) (h : s ≤ t) :
    Function.Surjective (Quotient.map id (fun _ _ hr => h hr) : Quotient s → Quotient t) := by
  intro x
  induction x using Quotient.inductionOn with
  | h a => exact ⟨Quotient.mk _ a, rfl⟩

private theorem setoid_eq_of_le_card_quotient_eq {k : ℕ} (s t : Setoid (Fin k))
    (h : s ≤ t) (hc : Fintype.card (Quotient s) = Fintype.card (Quotient t)) : s = t := by
  let f : Quotient s → Quotient t := Quotient.map id (fun _ _ hr => h hr)
  have hs : Function.Surjective f := quotient_map_surjective s t h
  have hi : Function.Injective f := by
    by_contra hn
    have hlt := Fintype.card_lt_of_surjective_not_injective f hs hn
    omega
  apply le_antisymm h
  intro a b hr
  exact Quotient.exact (hi (show f (Quotient.mk _ a) = f (Quotient.mk _ b) from Quotient.sound hr))

/-- Joining ordinary pairings can only decrease their genuine number of classes. -/
theorem pairingLoopCount_le {r : ℕ} (p q : OrdinaryPairing r) : pairingLoopCount p q ≤ r := by
  have h := Fintype.card_le_of_surjective _
    (quotient_map_surjective (pairingSetoid p.out) (pairingSetoid p.out ⊔ pairingSetoid q.out) le_sup_left)
  simpa only [pairingLoopCount, card_pairingSetoid_quotient] using h

/-- The maximal loop count occurs precisely on the intrinsic pairing diagonal. -/
theorem pairingLoopCount_eq_iff {r : ℕ} (p q : OrdinaryPairing r) :
    pairingLoopCount p q = r ↔ p = q := by
  constructor
  · intro hc
    have hp : pairingSetoid p.out = pairingSetoid p.out ⊔ pairingSetoid q.out :=
      setoid_eq_of_le_card_quotient_eq _ _ le_sup_left
        ((card_pairingSetoid_quotient p.out).trans hc.symm)
    have hq : pairingSetoid q.out = pairingSetoid p.out :=
      setoid_eq_of_le_card_quotient_eq _ _ (hp ▸ le_sup_right)
        ((card_pairingSetoid_quotient q.out).trans (card_pairingSetoid_quotient p.out).symm)
    have he : (Quotient.mk _ p.out : OrdinaryPairing r) = Quotient.mk _ q.out := Quotient.sound hq.symm
    simpa only [Quotient.out_eq] using he
  · rintro rfl
    simp only [pairingLoopCount, sup_idem, card_pairingSetoid_quotient]

/-- Off-diagonal ordinary joins have strictly fewer loops than the pair count. -/
theorem pairingLoopCount_lt_of_ne {r : ℕ} (p q : OrdinaryPairing r) (h : p ≠ q) :
    pairingLoopCount p q < r :=
  lt_of_le_of_ne (pairingLoopCount_le p q) (fun he => h ((pairingLoopCount_eq_iff p q).mp he))
end FreeProbability.Orthogonal

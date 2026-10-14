import FreeProbability.RandomMatrix.OrthogonalPairingDistance

/-! # Intrinsic ordinary pairing involutions and genuine join components -/

noncomputable section
open scoped Classical
namespace FreeProbability.Orthogonal

/-- Exchange the two actual sites in each pair of a pairing code. -/
def codePairingPartner {r : ℕ} (e : PairingSites r) : Equiv.Perm (Fin (2 * r)) :=
  (e.trans (Equiv.prodCongr (Equiv.refl (Fin r)) (Equiv.swap 0 1))).trans e.symm

private theorem codePairingPartner_apply {r : ℕ} (e : PairingSites r) (a : Fin (2 * r)) :
    codePairingPartner e a = e.symm ((e a).1, Equiv.swap 0 1 (e a).2) := rfl

theorem codePairingPartner_involutive {r : ℕ} (e : PairingSites r) :
    Function.Involutive (codePairingPartner e) := by
  intro a
  simp only [codePairingPartner_apply, Equiv.apply_symm_apply, Equiv.swap_apply_self, Prod.mk.eta,
    Equiv.symm_apply_apply]

theorem codePairingPartner_ne_self {r : ℕ} (e : PairingSites r) (a : Fin (2 * r)) :
    codePairingPartner e a ≠ a := by
  intro h
  have he := congrArg (fun x => (e x).2) h
  simp only [codePairingPartner_apply, Equiv.apply_symm_apply] at he
  have hn : Equiv.swap (0 : Fin 2) 1 (e a).2 ≠ (e a).2 := by
    have hswap := Equiv.swap_apply_ne_self_iff (a := (0 : Fin 2)) (b := 1) (x := (e a).2)
    apply hswap.mpr
    constructor
    · decide
    · have h : (e a).2 = 0 ∨ (e a).2 = 1 := by omega
      exact h
  exact hn he

/-- The actual partner is related to its original endpoint in the raw pairing. -/
theorem codePairingPartner_related {r : ℕ} (e : PairingSites r) (a : Fin (2 * r)) :
    pairingSetoid e a (codePairingPartner e a) := by
  change (e a).1 = (e (codePairingPartner e a)).1
  simp only [codePairingPartner_apply, Equiv.apply_symm_apply]

/-- Two sites in a genuine pair are either equal or actual partners. -/
theorem pairingSetoid_iff_eq_or_codePartner {r : ℕ} (e : PairingSites r)
    (a b : Fin (2 * r)) :
    pairingSetoid e a b ↔ b = a ∨ b = codePairingPartner e a := by
  constructor
  · intro h
    change (e a).1 = (e b).1 at h
    by_cases he : (e a).2 = (e b).2
    · left
      apply e.injective
      exact Prod.ext h.symm he.symm
    · right
      apply e.injective
      rw [codePairingPartner_apply, Equiv.apply_symm_apply]
      apply Prod.ext
      · exact h.symm
      · have hb : (e b).2 = Equiv.swap 0 1 (e a).2 := by
          have ha0 : (e a).2 = 0 ∨ (e a).2 = 1 := by omega
          have hb0 : (e b).2 = 0 ∨ (e b).2 = 1 := by omega
          rcases ha0 with ha0 | ha0 <;> rcases hb0 with hb0 | hb0 <;>
            simp_all [Equiv.swap_apply_left, Equiv.swap_apply_right]
        exact hb
  · rintro (rfl | rfl)
    · exact (pairingSetoid e).refl _
    · exact codePairingPartner_related e a

/-- Raw relation equality makes the actual partner independent of all code
orientations and pair numbering. -/
theorem codePairingPartner_eq_of_setoid_eq {r : ℕ} (e f : PairingSites r)
    (h : pairingSetoid e = pairingSetoid f) : codePairingPartner e = codePairingPartner f := by
  apply Equiv.ext
  intro a
  have he : pairingSetoid f a (codePairingPartner e a) := h ▸ codePairingPartner_related e a
  rcases (pairingSetoid_iff_eq_or_codePartner f a _).mp he with he | he
  · exact False.elim (codePairingPartner_ne_self e a he)
  · exact he

/-- The genuine intrinsic ordinary pairing partner involution. -/
def pairingPartner {r : ℕ} (p : OrdinaryPairing r) : Equiv.Perm (Fin (2 * r)) :=
  codePairingPartner p.out

/-- Evaluating on any code recovers its actual partner map. -/
theorem pairingPartner_mk {r : ℕ} (e : PairingSites r) :
    pairingPartner (Quotient.mk _ e) = codePairingPartner e := by
  apply codePairingPartner_eq_of_setoid_eq
  have h := Quotient.exact (Quotient.out_eq (Quotient.mk (Setoid.ker pairingSetoid) e))
  exact h

theorem pairingPartner_involutive {r : ℕ} (p : OrdinaryPairing r) :
    Function.Involutive (pairingPartner p) := codePairingPartner_involutive p.out

theorem pairingPartner_ne_self {r : ℕ} (p : OrdinaryPairing r) (a : Fin (2 * r)) :
    pairingPartner p a ≠ a := codePairingPartner_ne_self p.out a

theorem pairingSetoid_iff_eq_or_partner {r : ℕ} (p : OrdinaryPairing r)
    (a b : Fin (2 * r)) :
    pairingSetoid p.out a b ↔ b = a ∨ b = pairingPartner p a :=
  pairingSetoid_iff_eq_or_codePartner p.out a b

theorem pairingPartner_related {r : ℕ} (p : OrdinaryPairing r) (a : Fin (2 * r)) :
    pairingSetoid p.out a (pairingPartner p a) := codePairingPartner_related p.out a

/-- The actual partner permutation completely determines the intrinsic pairing. -/
theorem pairingPartner_eq_iff {r : ℕ} (p q : OrdinaryPairing r) :
    pairingPartner p = pairingPartner q ↔ p = q := by
  constructor
  · intro h
    have he : pairingSetoid p.out = pairingSetoid q.out := by
      ext a b
      rw [pairingSetoid_iff_eq_or_partner, pairingSetoid_iff_eq_or_partner, h]
    have hquot : (Quotient.mk _ p.out : OrdinaryPairing r) = Quotient.mk _ q.out := Quotient.sound he
    simpa only [Quotient.out_eq] using hquot
  · rintro rfl
    rfl

/-- One genuine move under either of the two actual pairing involutions. -/
def pairingMoves {r : ℕ} (p q : OrdinaryPairing r) (a b : Fin (2 * r)) : Prop :=
  pairingPartner p a = b ∨ pairingPartner q a = b

theorem pairingMoves_symmetric {r : ℕ} (p q : OrdinaryPairing r) :
    Std.Symm (pairingMoves p q) := by
  constructor
  intro a b h
  rcases h with h | h
  · left
    rw [← h, pairingPartner_involutive p]
  · right
    rw [← h, pairingPartner_involutive q]

/-- The raw ordinary join is exactly the relation generated by the two
actual partner moves. -/
theorem pairingJoin_eq_partner_moves {r : ℕ} (p q : OrdinaryPairing r) :
    pairingSetoid p.out ⊔ pairingSetoid q.out = Relation.EqvGen.setoid (pairingMoves p q) := by
  apply le_antisymm
  · apply sup_le
    · intro a b hab
      rcases (pairingSetoid_iff_eq_or_partner p a b).mp hab with rfl | h
      · exact Relation.EqvGen.refl _
      · exact Relation.EqvGen.rel _ _ (Or.inl h.symm)
    · intro a b hab
      rcases (pairingSetoid_iff_eq_or_partner q a b).mp hab with rfl | h
      · exact Relation.EqvGen.refl _
      · exact Relation.EqvGen.rel _ _ (Or.inr h.symm)
  · apply Setoid.eqvGen_le
    intro a b hab
    rcases hab with h | h
    · exact (show pairingSetoid p.out ≤ pairingSetoid p.out ⊔ pairingSetoid q.out from le_sup_left)
        ((pairingSetoid_iff_eq_or_partner p a b).mpr (Or.inr h.symm))
    · exact (show pairingSetoid q.out ≤ pairingSetoid p.out ⊔ pairingSetoid q.out from le_sup_right)
        ((pairingSetoid_iff_eq_or_partner q a b).mpr (Or.inr h.symm))

/-- Raw join components are genuine finite orbits under the two pairing
involutions, expressed as reflexive transitive reachability. -/
theorem pairingJoin_related_iff_reachable {r : ℕ} (p q : OrdinaryPairing r)
    (a b : Fin (2 * r)) :
    (pairingSetoid p.out ⊔ pairingSetoid q.out) a b ↔
      Relation.ReflTransGen (pairingMoves p q) a b := by
  let : Std.Symm (pairingMoves p q) := pairingMoves_symmetric p q
  rw [pairingJoin_eq_partner_moves]
  change Relation.EqvGen (pairingMoves p q) a b ↔ _
  rw [Relation.EqvGen.eqvGen_eq_reflTransGen]

/-- The existing loop count is the actual number of these partner components. -/
theorem pairingLoopCount_eq_partner_components {r : ℕ} (p q : OrdinaryPairing r) :
    pairingLoopCount p q = Fintype.card (Quotient (Relation.EqvGen.setoid (pairingMoves p q))) := by
  unfold pairingLoopCount
  rw [pairingJoin_eq_partner_moves]

end FreeProbability.Orthogonal

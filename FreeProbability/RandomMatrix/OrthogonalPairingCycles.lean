import FreeProbability.RandomMatrix.OrthogonalPairingPartner
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Algebra.Ring.Int.Parity

/-! # Genuine alternating involution components and disjoint half-orbits -/

noncomputable section
open scoped Classical
namespace FreeProbability.Orthogonal
open Equiv.Perm

private theorem involution_inverse {α : Type*} (P : Equiv.Perm α)
    (hP : Function.Involutive P) : P⁻¹ = P := by
  apply Equiv.ext
  intro a
  apply P.injective
  change P (P.symm a) = P (P a)
  rw [Equiv.apply_symm_apply, hP a]

/-- An actual involution reverses every integer power of the alternating
product of two actual involutions. No finiteness assumption is needed. -/
theorem involutionProduct_reverse_zpow {α : Type*} (P Q : Equiv.Perm α)
    (hP : Function.Involutive P) (hQ : Function.Involutive Q) (k : ℤ) (a : α) :
    P (((P * Q) ^ k) a) = ((P * Q) ^ (-k)) (P a) := by
  have hiP := involution_inverse P hP
  have hiQ := involution_inverse Q hQ
  have hPP : P * P = 1 := by ext a; exact hP a
  have hs : SemiconjBy P (P * Q) (P * Q)⁻¹ := by
    change P * (P * Q) = (P * Q)⁻¹ * P
    rw [_root_.mul_inv_rev, hiP, hiQ]
    simp only [← mul_assoc, hPP, one_mul]
    rw [mul_assoc, hPP, mul_one]
  have hz := hs.zpow_right k
  change P * (P * Q) ^ k = ((P * Q)⁻¹) ^ k * P at hz
  have he := congrArg (fun T : Equiv.Perm α => T a) hz
  simpa only [Equiv.Perm.mul_apply, inv_zpow, ← zpow_neg] using he

/-- Fixed-point-free involutions give genuinely distinct half-orbits of their
product. The even/odd exponent obstruction is proved, not assumed. -/
theorem involutionProduct_not_sameCycle_partner {α : Type*} (P Q : Equiv.Perm α)
    (hP : Function.Involutive P) (hQ : Function.Involutive Q)
    (hPn : ∀ a, P a ≠ a) (hQn : ∀ a, Q a ≠ a) (a : α) :
    ¬ SameCycle (P * Q) a (P a) := by
  rintro ⟨k, hk⟩
  obtain ⟨l, hl | hl⟩ := Int.even_or_odd' k
  · have he := involutionProduct_reverse_zpow P Q hP hQ l a
    rw [← hk] at he
    simp only [← Equiv.Perm.mul_apply, ← zpow_add] at he
    have hexp : -l + k = l := by omega
    rw [hexp] at he
    exact hPn (((P * Q) ^ l) a) he
  · have hQeq : ∀ b, Q b = P ((P * Q) b) := by
      intro b
      simp only [Equiv.Perm.mul_apply]
      exact (hP (Q b)).symm
    have he := involutionProduct_reverse_zpow P Q hP hQ (l + 1) a
    rw [← hk] at he
    simp only [← Equiv.Perm.mul_apply, ← zpow_add] at he
    have hexp : -(l + 1) + k = l := by omega
    rw [hexp, zpow_add_one] at he
    simp only [Equiv.Perm.mul_apply] at he
    have hc : ((P * Q) ^ l) ((P * Q) a) = (P * Q) (((P * Q) ^ l) a) :=
      by simpa only [zpow_one] using Equiv.Perm.zpow_apply_comm (P * Q) l 1
    change P (((P * Q) ^ l) ((P * Q) a)) = ((P * Q) ^ l) a at he
    rw [hc, ← hQeq] at he
    exact hQn (((P * Q) ^ l) a) he

private theorem sameCycle_partner {α : Type*} (P Q : Equiv.Perm α)
    (hP : Function.Involutive P) (hQ : Function.Involutive Q) {a b : α}
    (h : SameCycle (P * Q) a b) : SameCycle (P * Q) (P a) (P b) := by
  obtain ⟨k, hk⟩ := h
  exact ⟨-k, by rw [← involutionProduct_reverse_zpow P Q hP hQ, hk]⟩

private def twoOrbitSetoid {α : Type*} (P Q : Equiv.Perm α)
    (hP : Function.Involutive P) (hQ : Function.Involutive Q) : Setoid α where
  r a b := SameCycle (P * Q) a b ∨ SameCycle (P * Q) (P a) b
  iseqv := {
    refl := fun a => Or.inl (SameCycle.refl _ a)
    symm := by
      intro a b h
      rcases h with h | h
      · exact Or.inl h.symm
      · have he := sameCycle_partner P Q hP hQ h
        rw [hP] at he
        exact Or.inr he.symm
    trans := by
      intro a b c hab hbc
      rcases hab with hab | hab <;> rcases hbc with hbc | hbc
      · exact Or.inl (hab.trans hbc)
      · exact Or.inr ((sameCycle_partner P Q hP hQ hab).trans hbc)
      · exact Or.inr (hab.trans hbc)
      · have he := sameCycle_partner P Q hP hQ hab
        rw [hP] at he
        exact Or.inl (he.trans hbc) }

private theorem sameCycle_le_component {α : Type*} (P Q : Equiv.Perm α)
    (hP : Function.Involutive P) (hQ : Function.Involutive Q) :
    SameCycle.setoid (P * Q) ≤ Relation.EqvGen.setoid (fun a b => P a = b ∨ Q a = b) := by
  let C := Relation.EqvGen.setoid (fun a b => P a = b ∨ Q a = b)
  have hforward (a : α) : C a ((P * Q) a) :=
    C.trans (Relation.EqvGen.rel _ _ (Or.inr rfl)) (Relation.EqvGen.rel _ _ (Or.inl rfl))
  have hbackward (a : α) : C a ((P * Q)⁻¹ a) := by
    rw [_root_.mul_inv_rev, involution_inverse P hP, involution_inverse Q hQ]
    exact C.trans (Relation.EqvGen.rel _ _ (Or.inl rfl)) (Relation.EqvGen.rel _ _ (Or.inr rfl))
  have hpow (T : Equiv.Perm α) (hT : ∀ a, C a (T a)) (m : ℕ) (a : α) : C a ((T ^ m) a) := by
    induction m with
    | zero => exact C.refl a
    | succ m ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact C.trans ih (hT _)
  intro a b hab
  obtain ⟨k, rfl⟩ := hab
  cases k with
  | ofNat m =>
    change C a (((P * Q) ^ (m : ℤ)) a)
    rw [zpow_natCast]
    exact hpow (P * Q) hforward m a
  | negSucc m => simpa only [zpow_negSucc, inv_pow] using hpow (P * Q)⁻¹ hbackward (m + 1) a

/-- The actual component generated by two involutions is exactly the union
of the two product orbits. Fixed-point freedom is not needed for this identity. -/
theorem involutionComponent_iff_two_product_orbits {α : Type*} (P Q : Equiv.Perm α)
    (hP : Function.Involutive P) (hQ : Function.Involutive Q) (a b : α) :
    Relation.EqvGen (fun x y => P x = y ∨ Q x = y) a b ↔
      SameCycle (P * Q) a b ∨ SameCycle (P * Q) (P a) b := by
  have hle : Relation.EqvGen.setoid (fun x y => P x = y ∨ Q x = y) ≤ twoOrbitSetoid P Q hP hQ := by
    apply Setoid.eqvGen_le
    intro x y h
    rcases h with rfl | rfl
    · exact Or.inr (SameCycle.refl _ _)
    · right
      have he : (P * Q) (Q x) = P x := by
        simp only [Equiv.Perm.mul_apply]
        rw [hQ x]
      exact SameCycle.symm (show SameCycle (P * Q) (Q x) (P x) from
        ⟨1, by simpa only [zpow_one] using he⟩)
  constructor
  · intro h
    exact hle h
  · rintro (h | h)
    · exact sameCycle_le_component P Q hP hQ h
    · exact (Relation.EqvGen.setoid _).trans (Relation.EqvGen.rel _ _ (Or.inl rfl))
        (sameCycle_le_component P Q hP hQ h)

/-- The genuine product permutation traversing alternate pairing edges. -/
def pairingCyclePermutation {r : ℕ} (p q : OrdinaryPairing r) : Equiv.Perm (Fin (2 * r)) :=
  pairingPartner p * pairingPartner q

/-- Every raw pairing component consists exactly of two product half-orbits. -/
theorem pairingJoin_related_iff_two_cycles {r : ℕ} (p q : OrdinaryPairing r)
    (a b : Fin (2 * r)) :
    (pairingSetoid p.out ⊔ pairingSetoid q.out) a b ↔
      SameCycle (pairingCyclePermutation p q) a b ∨
        SameCycle (pairingCyclePermutation p q) (pairingPartner p a) b := by
  rw [pairingJoin_eq_partner_moves]
  exact involutionComponent_iff_two_product_orbits _ _
    (pairingPartner_involutive p) (pairingPartner_involutive q) a b

/-- The two half-orbits in each ACTUAL pairing component are disjoint. -/
theorem pairingCycle_not_sameCycle_partner {r : ℕ} (p q : OrdinaryPairing r)
    (a : Fin (2 * r)) :
    ¬ SameCycle (pairingCyclePermutation p q) a (pairingPartner p a) :=
  involutionProduct_not_sameCycle_partner _ _ (pairingPartner_involutive p)
    (pairingPartner_involutive q) (pairingPartner_ne_self p) (pairingPartner_ne_self q) a

/-- The actual partner exchanges the two product half-orbits bijectively. -/
theorem pairingCycle_sameCycle_partner_iff {r : ℕ} (p q : OrdinaryPairing r)
    (a b : Fin (2 * r)) :
    SameCycle (pairingCyclePermutation p q) (pairingPartner p a) (pairingPartner p b) ↔
      SameCycle (pairingCyclePermutation p q) a b := by
  constructor
  · intro h
    have he := sameCycle_partner _ _ (pairingPartner_involutive p)
      (pairingPartner_involutive q) h
    rw [pairingPartner_involutive p a, pairingPartner_involutive p b] at he
    exact he
  · exact sameCycle_partner _ _ (pairingPartner_involutive p) (pairingPartner_involutive q)

/-- The two half-orbits are disjoint as actual sets of sites. -/
theorem pairingCycle_half_orbits_disjoint {r : ℕ} (p q : OrdinaryPairing r)
    (a : Fin (2 * r)) :
    Disjoint {b | SameCycle (pairingCyclePermutation p q) a b}
      {b | SameCycle (pairingCyclePermutation p q) (pairingPartner p a) b} := by
  apply Set.disjoint_left.mpr
  intro b hb₁ hb₂
  exact pairingCycle_not_sameCycle_partner p q a (SameCycle.trans hb₁ (SameCycle.symm hb₂))

/-- A doubled edge gives the identity product, hence two singleton half-orbits. -/
theorem pairingCyclePermutation_self {r : ℕ} (p : OrdinaryPairing r) :
    pairingCyclePermutation p p = 1 := by
  apply Equiv.ext
  intro a
  exact pairingPartner_involutive p a

/-- The empty site type has no product orbits in degree zero. -/
theorem pairingCycle_orbit_card_zero (p q : OrdinaryPairing 0) :
    Fintype.card (Quotient (SameCycle.setoid (pairingCyclePermutation p q))) = 0 := by
  apply Fintype.card_eq_zero_iff.mpr
  constructor
  intro x
  induction x using Quotient.inductionOn with
  | h a => exact Fin.elim0 a

end FreeProbability.Orthogonal

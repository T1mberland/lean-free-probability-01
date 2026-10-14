import FreeProbability.RandomMatrix.OrthogonalPairingHalfOrientation
import FreeProbability.RandomMatrix.OrthogonalPermutationNetwork

/-! # Actual selected-half components and compatible pairing colorings -/

noncomputable section
open scoped Classical
namespace FreeProbability.Orthogonal
open Equiv.Perm

/-- Actual product-cycle relation on selected sites is exactly raw component
membership. No quotient-count premise is supplied. -/
theorem pairingHalf_sameCycle_iff_component {r : ℕ} (p q : OrdinaryPairing r)
    (a b : PairingHalfSites p q) :
    SameCycle (pairingHalfPermutation p q) a b ↔
      (pairingSetoid p.out ⊔ pairingSetoid q.out) a.val b.val := by
  rw [pairingHalfPermutation, sameCycle_subtypePerm]
  constructor
  · intro h
    exact (pairingJoin_related_iff_two_cycles p q a.val b.val).mpr (Or.inl h)
  · intro h
    let c : PairingJoinComponents p q := Quotient.mk _ a.val
    have ha := (pairingHalf_iff_cycle_of_component p q c a.val rfl).mp a.property
    have hb := (pairingHalf_iff_cycle_of_component p q c b.val (Quotient.sound h).symm).mp b.property
    exact ha.symm.trans hb

/-- The ACTUAL quotient of selected cycles equals the actual raw join
component quotient, including fixed singleton cycles and degree zero. -/
def pairingHalfOrbitComponentEquiv {r : ℕ} (p q : OrdinaryPairing r) :
    PermutationOrbitIndex (pairingHalfPermutation p q) ≃ PairingJoinComponents p q := by
  let f : PairingHalfSites p q → PairingJoinComponents p q := fun a => Quotient.mk _ a.val
  have hs : Function.Surjective f := by
    intro c
    exact ⟨⟨c.out, pairingHalf_component_seed p q c⟩, Quotient.out_eq c⟩
  have he : SameCycle.setoid (pairingHalfPermutation p q) = Setoid.ker f := by
    ext a b
    change SameCycle (pairingHalfPermutation p q) a b ↔ f a = f b
    rw [pairingHalf_sameCycle_iff_component]
    exact ⟨Quotient.sound, Quotient.exact⟩
  exact (Quotient.congrRight (Setoid.ext_iff.mp he)).trans (Setoid.quotientKerEquivOfSurjective f hs)

/-- There is exactly one selected cycle per genuine raw loop. -/
theorem pairingHalf_orbit_card {r : ℕ} (p q : OrdinaryPairing r) :
    Fintype.card (PermutationOrbitIndex (pairingHalfPermutation p q)) = pairingLoopCount p q :=
  Fintype.card_congr (pairingHalfOrbitComponentEquiv p q)

/-- The chosen site representing an actual first-pairing class. -/
def pairingHalfRepresentative {r : ℕ} (p q : OrdinaryPairing r) (a : Fin (2 * r)) : PairingHalfSites p q :=
  if h : pairingHalf p q a then ⟨a, h⟩
  else ⟨pairingPartner p a, (pairingHalf_partner_iff p q a).mpr h⟩

theorem pairingHalfRepresentative_of_mem {r : ℕ} (p q : OrdinaryPairing r)
    (a : PairingHalfSites p q) : pairingHalfRepresentative p q a.val = a := by
  apply Subtype.ext
  simp only [pairingHalfRepresentative, a.property, dite_true]

theorem pairingHalfRepresentative_partner {r : ℕ} (p q : OrdinaryPairing r)
    (a : Fin (2 * r)) :
    pairingHalfRepresentative p q (pairingPartner p a) = pairingHalfRepresentative p q a := by
  apply Subtype.ext
  by_cases h : pairingHalf p q a
  · have hn : ¬ pairingHalf p q (pairingPartner p a) := by
      intro he
      exact (pairingHalf_partner_iff p q a).mp he h
    simp only [pairingHalfRepresentative, h, hn, dite_true, dite_false,
      pairingPartner_involutive p a]
  · have hm := (pairingHalf_partner_iff p q a).mpr h
    simp only [pairingHalfRepresentative, h, hm, dite_true, dite_false]

/-- Compatible colorings of the actual first pairing, with no finite color
space requirement. -/
abbrev PairingCompatibleColorings {r : ℕ} (p : OrdinaryPairing r) (n : Type*) :=
  {i : Fin (2 * r) → n // pairingSetoid p.out ≤ Setoid.ker i}

private theorem compatible_representative {r : ℕ} {n : Type*} (p q : OrdinaryPairing r)
    (i : PairingCompatibleColorings p n) (a : Fin (2 * r)) :
    i.val (pairingHalfRepresentative p q a).val = i.val a := by
  unfold pairingHalfRepresentative
  split
  · rfl
  · exact (i.property (pairingPartner_related p a)).symm

/-- Genuine pairing-compatible colorings are exactly arbitrary colorings of
the selected half. Both inverse identities are proved. -/
def pairingCompatibleColoringsEquiv {r : ℕ} (p q : OrdinaryPairing r) (n : Type*) :
    PairingCompatibleColorings p n ≃ (PairingHalfSites p q → n) where
  toFun i a := i.val a.val
  invFun v := ⟨fun a => v (pairingHalfRepresentative p q a), by
    intro a b hab
    rcases (pairingSetoid_iff_eq_or_partner p a b).mp hab with rfl | rfl
    · rfl
    · change v (pairingHalfRepresentative p q a) = v (pairingHalfRepresentative p q (pairingPartner p a))
      rw [pairingHalfRepresentative_partner]⟩
  left_inv i := by
    apply Subtype.ext
    funext a
    exact compatible_representative p q i a
  right_inv v := by
    funext a
    change v (pairingHalfRepresentative p q a.val) = v a
    rw [pairingHalfRepresentative_of_mem]

end FreeProbability.Orthogonal

import FreeProbability.RandomMatrix.OrthogonalPairingCycles

/-! # Genuine product-orbit counting, including singleton cycles -/

noncomputable section
open scoped Classical
namespace FreeProbability.Orthogonal
open Equiv.Perm

/-- ALL product-permutation orbits, including fixed singleton orbits. -/
abbrev PairingProductOrbits {r : ℕ} (p q : OrdinaryPairing r) :=
  Quotient (SameCycle.setoid (pairingCyclePermutation p q))

/-- Actual components of the raw ordinary pairing join. -/
abbrev PairingJoinComponents {r : ℕ} (p q : OrdinaryPairing r) :=
  Quotient (pairingSetoid p.out ⊔ pairingSetoid q.out)

/-- The actual map from a product orbit to its raw join component. -/
def pairingCycleComponentMap {r : ℕ} (p q : OrdinaryPairing r) :
    PairingProductOrbits p q → PairingJoinComponents p q :=
  Quotient.map id (fun a b h => (pairingJoin_related_iff_two_cycles p q a b).mpr (Or.inl h))

/-- Every genuine raw join component has product half-orbits. -/
theorem pairingCycleComponentMap_surjective {r : ℕ} (p q : OrdinaryPairing r) :
    Function.Surjective (pairingCycleComponentMap p q) := by
  intro c
  exact ⟨Quotient.mk _ c.out, Quotient.out_eq c⟩

private theorem component_partner_class {r : ℕ} (p q : OrdinaryPairing r)
    (a : Fin (2 * r)) :
    (Quotient.mk _ (pairingPartner p a) : PairingJoinComponents p q) = Quotient.mk _ a := by
  apply Quotient.sound
  apply (pairingSetoid p.out ⊔ pairingSetoid q.out).symm
  exact (show pairingSetoid p.out ≤ pairingSetoid p.out ⊔ pairingSetoid q.out from le_sup_left)
    (pairingPartner_related p a)

/-- The fiber is precisely the two ACTUAL half-orbit classes of a component
representative, without forgetting fixed singleton product orbits. -/
theorem pairingCycleComponentMap_fiber_iff {r : ℕ} (p q : OrdinaryPairing r)
    (c : PairingJoinComponents p q) (x : PairingProductOrbits p q) :
    pairingCycleComponentMap p q x = c ↔
      x = Quotient.mk _ c.out ∨ x = Quotient.mk _ (pairingPartner p c.out) := by
  induction x using Quotient.inductionOn with
  | h a =>
    constructor
    · intro h
      have he : (Quotient.mk _ c.out : PairingJoinComponents p q) = Quotient.mk _ a :=
        (Quotient.out_eq c).trans h.symm
      have hr := Quotient.exact he
      rcases (pairingJoin_related_iff_two_cycles p q c.out a).mp hr with hr | hr
      · left
        exact (Quotient.sound hr).symm
      · right
        exact (Quotient.sound hr).symm
    · rintro (h | h)
      · rw [h]
        exact Quotient.out_eq c
      · rw [h]
        exact (component_partner_class p q c.out).trans (Quotient.out_eq c)

/-- Each actual component fiber has exactly two elements, in every degree. -/
theorem pairingCycleComponentMap_fiber_card {r : ℕ} (p q : OrdinaryPairing r)
    (c : PairingJoinComponents p q) :
    Fintype.card {x : PairingProductOrbits p q // pairingCycleComponentMap p q x = c} = 2 := by
  let x₀ : PairingProductOrbits p q := Quotient.mk _ c.out
  let x₁ : PairingProductOrbits p q := Quotient.mk _ (pairingPartner p c.out)
  have hne : x₀ ≠ x₁ := by
    intro h
    exact pairingCycle_not_sameCycle_partner p q c.out (Quotient.exact h)
  rw [Fintype.card_of_subtype {x₀, x₁} (fun x => by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using
      (pairingCycleComponentMap_fiber_iff p q c x).symm)]
  exact Finset.card_pair hne

/-- The number of genuine product-permutation orbits is twice the actual
raw join loop count. Includes degree zero and doubled edges. -/
theorem pairingCycle_orbit_card_eq_twice_loopCount {r : ℕ} (p q : OrdinaryPairing r) :
    Fintype.card (PairingProductOrbits p q) = 2 * pairingLoopCount p q := by
  calc
    _ = Fintype.card (Σ c : PairingJoinComponents p q,
        {x : PairingProductOrbits p q // pairingCycleComponentMap p q x = c}) :=
      (Fintype.card_congr (Equiv.sigmaFiberEquiv (pairingCycleComponentMap p q))).symm
    _ = ∑ _c : PairingJoinComponents p q, 2 := by
      rw [Fintype.card_sigma]
      apply Finset.sum_congr rfl
      intro c _
      exact pairingCycleComponentMap_fiber_card p q c
    _ = 2 * pairingLoopCount p q := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact Nat.mul_comm _ _

end FreeProbability.Orthogonal

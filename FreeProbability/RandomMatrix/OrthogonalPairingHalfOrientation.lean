import FreeProbability.RandomMatrix.OrthogonalPairingCycleCount

/-! # Actual chosen half-orbits and deterministic-edge orientations -/

noncomputable section
open scoped Classical
namespace FreeProbability.Orthogonal
open Equiv.Perm

private def siteComponent {r : ℕ} (p q : OrdinaryPairing r) (a : Fin (2 * r)) :
    PairingJoinComponents p q := Quotient.mk _ a

private theorem siteComponent_partner {r : ℕ} (p q : OrdinaryPairing r) (a : Fin (2 * r)) :
    siteComponent p q (pairingPartner p a) = siteComponent p q a := by
  apply Quotient.sound
  apply (pairingSetoid p.out ⊔ pairingSetoid q.out).symm
  exact (show pairingSetoid p.out ≤ pairingSetoid p.out ⊔ pairingSetoid q.out from le_sup_left)
    (pairingPartner_related p a)

private theorem siteComponent_rotate {r : ℕ} (p q : OrdinaryPairing r) (a : Fin (2 * r)) :
    siteComponent p q (pairingCyclePermutation p q a) = siteComponent p q a := by
  apply Quotient.sound
  apply (pairingSetoid p.out ⊔ pairingSetoid q.out).symm
  apply (pairingJoin_related_iff_two_cycles p q a _).mpr
  exact Or.inl ⟨1, rfl⟩

/-- Choose the actual product orbit of one genuine representative in each raw
join component. No orientation or bipartition premise is supplied. -/
def pairingHalf {r : ℕ} (p q : OrdinaryPairing r) (a : Fin (2 * r)) : Prop :=
  SameCycle (pairingCyclePermutation p q) (siteComponent p q a).out a

/-- The chosen half is invariant under the actual alternating product. -/
theorem pairingHalf_rotate_iff {r : ℕ} (p q : OrdinaryPairing r) (a : Fin (2 * r)) :
    pairingHalf p q (pairingCyclePermutation p q a) ↔ pairingHalf p q a := by
  unfold pairingHalf
  rw [siteComponent_rotate, sameCycle_apply_right]

/-- Membership is exactly the chosen actual orbit for the given raw component. -/
theorem pairingHalf_iff_cycle_of_component {r : ℕ} (p q : OrdinaryPairing r)
    (c : PairingJoinComponents p q) (a : Fin (2 * r))
    (hc : (Quotient.mk _ a : PairingJoinComponents p q) = c) :
    pairingHalf p q a ↔ SameCycle (pairingCyclePermutation p q) c.out a := by
  unfold pairingHalf siteComponent
  rw [hc]

/-- Each raw component's chosen representative actually belongs to its half. -/
theorem pairingHalf_component_seed {r : ℕ} (p q : OrdinaryPairing r)
    (c : PairingJoinComponents p q) : pairingHalf p q c.out := by
  exact (pairingHalf_iff_cycle_of_component p q c c.out (Quotient.out_eq c)).mpr (SameCycle.refl _ _)

/-- The first genuine partner exchanges the chosen half and its complement. -/
theorem pairingHalf_partner_iff {r : ℕ} (p q : OrdinaryPairing r) (a : Fin (2 * r)) :
    pairingHalf p q (pairingPartner p a) ↔ ¬ pairingHalf p q a := by
  let c := siteComponent p q a
  have hc : (pairingSetoid p.out ⊔ pairingSetoid q.out) c.out a :=
    Quotient.exact (Quotient.out_eq c)
  have hor := (pairingJoin_related_iff_two_cycles p q c.out a).mp hc
  have hx : pairingHalf p q (pairingPartner p a) ↔
      SameCycle (pairingCyclePermutation p q) (pairingPartner p c.out) a := by
    unfold pairingHalf
    rw [siteComponent_partner]
    have h := pairingCycle_sameCycle_partner_iff p q (pairingPartner p c.out) a
    rw [pairingPartner_involutive p c.out] at h
    exact h
  rw [hx]
  change SameCycle (pairingCyclePermutation p q) (pairingPartner p c.out) a ↔
    ¬ SameCycle (pairingCyclePermutation p q) c.out a
  constructor
  · intro h h'
    exact pairingCycle_not_sameCycle_partner p q c.out (h'.trans h.symm)
  · intro h
    exact hor.resolve_left h

/-- The second genuine partner also exchanges the two chosen halves. -/
theorem pairingHalf_second_partner_iff {r : ℕ} (p q : OrdinaryPairing r) (a : Fin (2 * r)) :
    pairingHalf p q (pairingPartner q a) ↔ ¬ pairingHalf p q a := by
  have he : pairingPartner q a = pairingPartner p (pairingCyclePermutation p q a) :=
    (pairingPartner_involutive p (pairingPartner q a)).symm
  rw [he, pairingHalf_partner_iff, pairingHalf_rotate_iff]

abbrev PairingHalfSites {r : ℕ} (p q : OrdinaryPairing r) := {a : Fin (2 * r) // pairingHalf p q a}

/-- The actual alternating product restricts to a genuine permutation of the
chosen half, including the empty half in degree zero. -/
def pairingHalfPermutation {r : ℕ} (p q : OrdinaryPairing r) : Equiv.Perm (PairingHalfSites p q) :=
  (pairingCyclePermutation p q).subtypePerm (pairingHalf_rotate_iff p q)

theorem pairingHalfPermutation_apply {r : ℕ} (p q : OrdinaryPairing r)
    (a : PairingHalfSites p q) : (pairingHalfPermutation p q a).val = pairingCyclePermutation p q a.val := rfl

private theorem code_endpoint_partner {r : ℕ} (e : PairingSites r) (k : Fin r) (b : Fin 2) :
    pairingPartner (Quotient.mk _ e) (e.symm (k, b)) = e.symm (k, Equiv.swap 0 1 b) := by
  rw [pairingPartner_mk]
  simp [codePairingPartner]

/-- Actual orientation of each deterministic edge: false selects endpoint
zero, true selects endpoint one. -/
def pairingEdgeOrientation {r : ℕ} (p : OrdinaryPairing r) (e : PairingSites r) (k : Fin r) : Bool :=
  if pairingHalf p (Quotient.mk _ e) (e.symm (k, 0)) then false else true

/-- Exactly one genuine endpoint of each deterministic edge is selected. -/
def pairingSelectedEndpoint {r : ℕ} (p : OrdinaryPairing r) (e : PairingSites r) (k : Fin r) :
    PairingHalfSites p (Quotient.mk _ e) :=
  if h : pairingHalf p (Quotient.mk _ e) (e.symm (k, 0)) then ⟨e.symm (k, 0), h⟩
  else ⟨e.symm (k, 1), by
    have he := (pairingHalf_second_partner_iff p (Quotient.mk _ e) (e.symm (k, 0))).mpr h
    simpa only [code_endpoint_partner, Equiv.swap_apply_left] using he⟩

private theorem selectedEndpoint_pair_label {r : ℕ} (p : OrdinaryPairing r)
    (e : PairingSites r) (k : Fin r) : (e (pairingSelectedEndpoint p e k).val).1 = k := by
  unfold pairingSelectedEndpoint
  split <;> simp only [Equiv.apply_symm_apply]

/-- Genuine exhaustion: every deterministic edge contributes exactly one
selected site, giving an actual edge-label equivalence with the chosen half. -/
def pairingEdgeHalfEquiv {r : ℕ} (p : OrdinaryPairing r) (e : PairingSites r) :
    Fin r ≃ PairingHalfSites p (Quotient.mk _ e) :=
  Equiv.ofBijective (pairingSelectedEndpoint p e) (by
    constructor
    · intro k l h
      have he := congrArg (fun a => (e a.val).1) h
      simpa only [selectedEndpoint_pair_label] using he
    · intro a
      let k := (e a.val).1
      have ha : a.val = e.symm (k, (e a.val).2) := by simp only [k, Prod.mk.eta, Equiv.symm_apply_apply]
      have hb : (e a.val).2 = 0 ∨ (e a.val).2 = 1 := by omega
      refine ⟨k, Subtype.ext ?_⟩
      rcases hb with hb | hb
      · have hm : pairingHalf p (Quotient.mk _ e) (e.symm (k, 0)) := by rw [← hb, ← ha]; exact a.property
        simp only [pairingSelectedEndpoint, hm, dite_true]
        exact (ha.trans (congrArg (fun b => e.symm (k, b)) hb)).symm
      · have hn : ¬ pairingHalf p (Quotient.mk _ e) (e.symm (k, 0)) := by
          have hm : pairingHalf p (Quotient.mk _ e) (e.symm (k, 1)) := by rw [← hb, ← ha]; exact a.property
          have he := (pairingHalf_second_partner_iff p (Quotient.mk _ e) (e.symm (k, 0))).mp
            (by simpa only [code_endpoint_partner, Equiv.swap_apply_left] using hm)
          exact he
        simp only [pairingSelectedEndpoint, hn, dite_false]
        exact (ha.trans (congrArg (fun b => e.symm (k, b)) hb)).symm)

theorem pairingEdgeHalfEquiv_apply {r : ℕ} (p : OrdinaryPairing r) (e : PairingSites r)
    (k : Fin r) : pairingEdgeHalfEquiv p e k = pairingSelectedEndpoint p e k := rfl

/-- The inverse equivalence recovers the actual deterministic edge label. -/
theorem pairingEdgeHalfEquiv_symm_apply {r : ℕ} (p : OrdinaryPairing r) (e : PairingSites r)
    (a : PairingHalfSites p (Quotient.mk _ e)) :
    (pairingEdgeHalfEquiv p e).symm a = (e a.val).1 := by
  have he := selectedEndpoint_pair_label p e ((pairingEdgeHalfEquiv p e).symm a)
  change (e ((pairingEdgeHalfEquiv p e) ((pairingEdgeHalfEquiv p e).symm a)).val).1 = _ at he
  rw [Equiv.apply_symm_apply] at he
  exact he.symm

/-- The actual code coordinate equals the proved chosen orientation. -/
theorem pairingSelectedEndpoint_coordinate {r : ℕ} (p : OrdinaryPairing r) (e : PairingSites r)
    (k : Fin r) :
    e (pairingSelectedEndpoint p e k).val = (k, if pairingEdgeOrientation p e k then 1 else 0) := by
  unfold pairingSelectedEndpoint pairingEdgeOrientation
  split <;> simp only [Equiv.apply_symm_apply, Bool.false_eq_true, ite_false, ite_true]

/-- The chosen half has exactly one site per deterministic pairing edge. -/
theorem pairingHalfSites_card {r : ℕ} (p q : OrdinaryPairing r) :
    Fintype.card (PairingHalfSites p q) = r := by
  have he := Fintype.card_congr (pairingEdgeHalfEquiv p q.out)
  simpa only [Quotient.out_eq, Fintype.card_fin] using he.symm

end FreeProbability.Orthogonal

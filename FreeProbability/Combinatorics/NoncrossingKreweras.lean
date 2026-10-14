import FreeProbability.Combinatorics.NoncrossingLattice

/-!
# Kreweras complements by interval signatures

For odd positions carrying `p`, two even positions are in the same complementary
region exactly when every chord of `p` has the same half-open interval membership
at those positions. This construction avoids assuming a maximal complement.
-/

namespace FreeProbability.NoncrossingPartition

variable {n : ℕ}

/-- Equality of all chord interval signatures. -/
def krewerasSetoid (p : NoncrossingPartition n) : Setoid (Fin n) where
  r a b := ∀ u v, p.val.r u v → ((u ≤ a ∧ a < v) ↔ (u ≤ b ∧ b < v))
  iseqv := {
    refl := fun _ _ _ _ => Iff.rfl
    symm := fun h u v huv => (h u v huv).symm
    trans := fun h₁ h₂ u v huv => (h₁ u v huv).trans (h₂ u v huv) }

/-- Chord signature classes form a noncrossing partition. -/
theorem krewerasSetoid_nonCrossing (p : NoncrossingPartition n) :
    IsNoncrossing p.krewerasSetoid := by
  intro a b c d hab hbc hcd hac hbd u v huv
  have h₁ := hac u v huv
  have h₂ := hbd u v huv
  constructor
  · intro ha
    have hc := h₁.mp ha
    exact ⟨le_trans ha.1 hab.le, lt_trans hbc hc.2⟩
  · intro hb
    have hd := h₂.mp hb
    have hc : u ≤ c ∧ c < v := ⟨le_trans hb.1 hbc.le, lt_trans hcd hd.2⟩
    exact h₁.mpr hc

/-- The right Kreweras complement, with odd original and even complementary positions. -/
def kreweras (p : NoncrossingPartition n) : NoncrossingPartition n :=
  ⟨p.krewerasSetoid, p.krewerasSetoid_nonCrossing⟩

@[simp] theorem kreweras_rel (p : NoncrossingPartition n) (a b : Fin n) :
    p.kreweras.val.r a b ↔
      ∀ u v, p.val.r u v → ((u ≤ a ∧ a < v) ↔ (u ≤ b ∧ b < v)) := Iff.rfl

/-- The original position numbered `i` in the doubled word. -/
def oddPosition (i : Fin n) : Fin (2 * n) := ⟨2 * i.val, by omega⟩

/-- The complementary position immediately following original position `i`. -/
def evenPosition (i : Fin n) : Fin (2 * n) := ⟨2 * i.val + 1, by omega⟩

/-- Position in either constituent word of an alternating doubled word. -/
def halfPosition (i : Fin (2 * n)) : Fin n := ⟨i.val / 2, by omega⟩

@[simp] theorem halfPosition_even (i : Fin n) : halfPosition (evenPosition i) = i := by
  apply Fin.ext
  change (2 * i.val + 1) / 2 = i.val
  omega

/-- Interleave two partitions without identifying any original/complementary positions. -/
def interleaveSetoid (p q : NoncrossingPartition n) : Setoid (Fin (2 * n)) where
  r a b := a.val % 2 = b.val % 2 ∧
    if a.val % 2 = 0 then p.val.r (halfPosition a) (halfPosition b)
    else q.val.r (halfPosition a) (halfPosition b)
  iseqv := {
    refl := fun a => ⟨rfl, by split_ifs <;> first | exact p.val.refl _ | exact q.val.refl _⟩
    symm := fun {a b} h => ⟨h.1.symm, by
      by_cases ha : a.val % 2 = 0
      · have hb : b.val % 2 = 0 := h.1.symm.trans ha
        simpa only [ha, hb, ite_true] using p.val.symm (by simpa only [ha, ite_true] using h.2)
      · have hb : b.val % 2 ≠ 0 := by omega
        simpa only [ha, hb, ite_false] using q.val.symm (by simpa only [ha, ite_false] using h.2)⟩
    trans := fun {a b c} h₁ h₂ => ⟨h₁.1.trans h₂.1, by
      by_cases ha : a.val % 2 = 0
      · have hb : b.val % 2 = 0 := h₁.1.symm.trans ha
        simp only [ha, ite_true]
        exact p.val.trans (by simpa only [ha, ite_true] using h₁.2)
          (by simpa only [hb, ite_true] using h₂.2)
      · have hb : b.val % 2 ≠ 0 := by omega
        simp only [ha, ite_false]
        exact q.val.trans (by simpa only [ha, ite_false] using h₁.2)
          (by simpa only [hb, ite_false] using h₂.2)⟩ }

@[simp] theorem interleave_odd_odd (p q : NoncrossingPartition n) (a b : Fin n) :
    (interleaveSetoid p q).r (oddPosition a) (oddPosition b) ↔ p.val.r a b := by
  change ((2 * a.val) % 2 = (2 * b.val) % 2 ∧
    (if (2 * a.val) % 2 = 0 then p.val.r (halfPosition (oddPosition a)) (halfPosition (oddPosition b))
    else q.val.r (halfPosition (oddPosition a)) (halfPosition (oddPosition b)))) ↔ _
  simp [halfPosition, oddPosition]

@[simp] theorem interleave_even_even (p q : NoncrossingPartition n) (a b : Fin n) :
    (interleaveSetoid p q).r (evenPosition a) (evenPosition b) ↔ q.val.r a b := by
  change ((2 * a.val + 1) % 2 = (2 * b.val + 1) % 2 ∧
    (if (2 * a.val + 1) % 2 = 0 then p.val.r (halfPosition (evenPosition a)) (halfPosition (evenPosition b))
    else q.val.r (halfPosition (evenPosition a)) (halfPosition (evenPosition b)))) ↔ _
  simp only [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_eq_of_lt (by omega : 1 < 2),
    halfPosition_even, one_ne_zero, ite_false, true_and]

@[simp] theorem interleave_odd_even (p q : NoncrossingPartition n) (a b : Fin n) :
    ¬ (interleaveSetoid p q).r (oddPosition a) (evenPosition b) := by
  intro h
  have he : (2 * a.val) % 2 = (2 * b.val + 1) % 2 := h.1
  omega

private theorem halfPosition_lt {a b : Fin (2 * n)} (hab : a < b)
    (hpar : a.val % 2 = b.val % 2) : halfPosition a < halfPosition b := by
  change a.val / 2 < b.val / 2
  have hval : a.val < b.val := hab
  omega

/-- Every partition refining the chord signature complement is compatible
with the original partition on alternating positions. -/
theorem interleave_nonCrossing_of_le_kreweras (p q : NoncrossingPartition n)
    (hq : q ≤ p.kreweras) : IsNoncrossing (interleaveSetoid p q) := by
  intro a b c d hab hbc hcd hac hbd
  have hacpar := hac.1
  have hbdpar := hbd.1
  have habval : a.val < b.val := hab
  have hbcval : b.val < c.val := hbc
  have hcdval : c.val < d.val := hcd
  by_cases ha : a.val % 2 = 0
  · have hc : c.val % 2 = 0 := hacpar.symm.trans ha
    have hpr : p.val.r (halfPosition a) (halfPosition c) := by
      simpa only [ha, ite_true] using hac.2
    by_cases hb : b.val % 2 = 0
    · have hd : d.val % 2 = 0 := hbdpar.symm.trans hb
      have hqr : p.val.r (halfPosition b) (halfPosition d) := by
        simpa only [hb, ite_true] using hbd.2
      refine ⟨ha.trans hb.symm, ?_⟩
      simp only [ha, ite_true]
      exact p.property _ _ _ _ (halfPosition_lt hab (ha.trans hb.symm))
        (halfPosition_lt hbc (hb.trans hc.symm)) (halfPosition_lt hcd (hc.trans hd.symm)) hpr hqr
    · have hqr : q.val.r (halfPosition b) (halfPosition d) := by
        simpa only [hb, ite_false] using hbd.2
      have hsig := hq hqr (halfPosition a) (halfPosition c) hpr
      have hin : halfPosition a ≤ halfPosition b ∧ halfPosition b < halfPosition c := by
        change a.val / 2 ≤ b.val / 2 ∧ b.val / 2 < c.val / 2
        omega
      have hout := (hsig.mp hin).2
      change d.val / 2 < c.val / 2 at hout
      omega
  · have hc : c.val % 2 ≠ 0 := by omega
    have hqr : q.val.r (halfPosition a) (halfPosition c) := by
      simpa only [ha, ite_false] using hac.2
    by_cases hb : b.val % 2 = 0
    · have hpr : p.val.r (halfPosition b) (halfPosition d) := by
        simpa only [hb, ite_true] using hbd.2
      have hsig := hq hqr (halfPosition b) (halfPosition d) hpr
      have hin : halfPosition b ≤ halfPosition c ∧ halfPosition c < halfPosition d := by
        change b.val / 2 ≤ c.val / 2 ∧ c.val / 2 < d.val / 2
        omega
      have hout := (hsig.mpr hin).1
      change b.val / 2 ≤ a.val / 2 at hout
      omega
    · have hd : d.val % 2 ≠ 0 := by omega
      have hbr : q.val.r (halfPosition b) (halfPosition d) := by
        simpa only [hb, ite_false] using hbd.2
      have habpar : a.val % 2 = b.val % 2 := by omega
      have hbcpar : b.val % 2 = c.val % 2 := by omega
      have hcdpar : c.val % 2 = d.val % 2 := by omega
      refine ⟨habpar, ?_⟩
      simp only [ha, ite_false]
      exact q.property _ _ _ _ (halfPosition_lt hab habpar)
        (halfPosition_lt hbc hbcpar) (halfPosition_lt hcd hcdpar) hqr hbr

private theorem signature_of_interleave_nonCrossing (p q : NoncrossingPartition n)
    (hnc : IsNoncrossing (interleaveSetoid p q)) {a b : Fin n} (hab : a < b)
    (hqr : q.val.r a b) : p.kreweras.val.r a b := by
  intro u v huv
  have habval : a.val < b.val := hab
  constructor
  · intro ha
    refine ⟨le_trans ha.1 hab.le, ?_⟩
    by_contra hb
    have huval : u.val ≤ a.val := ha.1
    have hvval : a.val < v.val := ha.2
    have hbval : v.val ≤ b.val := le_of_not_gt hb
    have hcross := hnc (oddPosition u) (evenPosition a) (oddPosition v) (evenPosition b)
      (by change 2 * u.val < 2 * a.val + 1; omega)
      (by change 2 * a.val + 1 < 2 * v.val; omega)
      (by change 2 * v.val < 2 * b.val + 1; omega)
      ((interleave_odd_odd p q u v).mpr huv) ((interleave_even_even p q a b).mpr hqr)
    exact interleave_odd_even p q u a hcross
  · intro hb
    refine ⟨?_, lt_trans hab hb.2⟩
    by_contra ha
    have haval : a.val < u.val := lt_of_not_ge ha
    have huval : u.val ≤ b.val := hb.1
    have hvval : b.val < v.val := hb.2
    have hcross := hnc (evenPosition a) (oddPosition u) (evenPosition b) (oddPosition v)
      (by change 2 * a.val + 1 < 2 * u.val; omega)
      (by change 2 * u.val < 2 * b.val + 1; omega)
      (by change 2 * b.val + 1 < 2 * v.val; omega)
      ((interleave_even_even p q a b).mpr hqr) ((interleave_odd_odd p q u v).mpr huv)
    exact interleave_odd_even p q u a ((interleaveSetoid p q).symm hcross)

/-- The complement is the greatest compatible partition on complementary
positions: this is the defining maximality theorem for the actual Kreweras complement. -/
theorem interleave_nonCrossing_iff (p q : NoncrossingPartition n) :
    IsNoncrossing (interleaveSetoid p q) ↔ q ≤ p.kreweras := by
  constructor
  · intro hnc a b hab
    rcases lt_trichotomy a b with hlt | heq | hgt
    · exact signature_of_interleave_nonCrossing p q hnc hlt hab
    · subst b
      exact p.kreweras.val.refl a
    · exact p.kreweras.val.symm
        (signature_of_interleave_nonCrossing p q hnc hgt (q.val.symm hab))
  · exact interleave_nonCrossing_of_le_kreweras p q

/-- Interleaving a partition with its complement is genuinely noncrossing. -/
def interleaveKreweras (p : NoncrossingPartition n) : NoncrossingPartition (2 * n) :=
  ⟨interleaveSetoid p p.kreweras, interleave_nonCrossing_of_le_kreweras p p.kreweras le_rfl⟩

/-- Refining the original partition coarsens its right complement. -/
theorem kreweras_antitone : Antitone (kreweras : NoncrossingPartition n → NoncrossingPartition n) := by
  intro p q hp a b hab u v huv
  exact hab u v (hp huv)

@[simp] theorem kreweras_discrete : (discrete n).kreweras = indiscrete n := by
  apply Subtype.ext
  apply Setoid.ext
  intro a b
  change (∀ u v : Fin n, u = v → ((u ≤ a ∧ a < v) ↔ (u ≤ b ∧ b < v))) ↔ True
  simp only [iff_true]
  intro u v huv
  subst v
  constructor
  · intro h
    exact False.elim (not_lt_of_ge h.1 h.2)
  · intro h
    exact False.elim (not_lt_of_ge h.1 h.2)

@[simp] theorem kreweras_indiscrete : (indiscrete n).kreweras = discrete n := by
  apply Subtype.ext
  apply Setoid.ext
  intro a b
  change (∀ u v : Fin n, True → ((u ≤ a ∧ a < v) ↔ (u ≤ b ∧ b < v))) ↔ a = b
  constructor
  · intro h
    rcases lt_trichotomy a b with hab | heq | hba
    · have hc := (h a b trivial).mp ⟨le_rfl, hab⟩
      exact False.elim (lt_irrefl b hc.2)
    · exact heq
    · have hc := (h b a trivial).mpr ⟨le_rfl, hba⟩
      exact False.elim (lt_irrefl a hc.2)
  · intro h
    subst b
    intro _ _ _
    rfl

end FreeProbability.NoncrossingPartition

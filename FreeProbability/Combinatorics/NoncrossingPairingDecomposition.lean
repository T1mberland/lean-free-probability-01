import FreeProbability.Combinatorics.NoncrossingPairing
import FreeProbability.Combinatorics.NoncrossingRestriction

/-!
# Decomposition of noncrossing pairings at the partner of zero

The partner of the first position separates two invariant ordered intervals.
Restriction to either interval remains a genuine pairing. Inverse gluing gives
an equivalence between all pairings and the two interval pairings with their size index.
-/

namespace FreeProbability.NoncrossingPairing

variable {m n : ℕ}

/-- Restriction to an ordered subset closed under partners retains all two-point blocks. -/
theorem isPairing_restrict (p : NoncrossingPairing n) (f : Fin m ↪o Fin n)
    (hclosed : ∀ a, p.partner (f a) ∈ Set.range f) : (p.val.restrict f).IsPairing := by
  classical
  intro t ht
  rw [NoncrossingPartition.blocks_restrict] at ht
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨hs, ⟨a, ha⟩⟩ := Finset.mem_filter.mp hs
  have hfa := (NoncrossingPartition.mem_pullbackBlock f s a).mp ha
  have hrange : ∀ b ∈ s, b ∈ Set.range f := by
    intro b hb
    have hrel := (p.val.rel_iff_mem_block hs hfa b).mpr hb
    rcases (p.rel_iff (f a) b).mp hrel with h | h
    · exact h ▸ ⟨a, rfl⟩
    · exact h ▸ hclosed a
  rw [NoncrossingPartition.card_pullbackBlock f s hrange]
  exact p.property s hs

/-- Positions strictly inside the first pair have their partners strictly inside too. -/
theorem partner_inside_first (p : NoncrossingPairing (n + 2)) (a : Fin (n + 2))
    (ha0 : 0 < a) (haq : a < p.partner 0) :
    0 < p.partner a ∧ p.partner a < p.partner 0 := by
  have hne0 : p.partner a ≠ 0 := by
    intro h
    have he : a = p.partner 0 := by simpa using congrArg p.partner h
    exact (ne_of_lt haq) he
  have hneq : p.partner a ≠ p.partner 0 := by
    intro h
    have he : a = 0 := by simpa using congrArg p.partner h
    exact (ne_of_gt ha0) he
  constructor
  · change 0 < (p.partner a).val
    exact Nat.pos_of_ne_zero (fun h => hne0 (Fin.ext h))
  · by_contra h
    have hqp : p.partner 0 < p.partner a := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hneq)
    have hrel := p.val.property 0 a (p.partner 0) (p.partner a)
      ha0 haq hqp (p.rel_partner 0) (p.rel_partner a)
    rcases (p.rel_iff 0 a).mp hrel with he | he
    · exact (ne_of_gt ha0) he
    · exact (ne_of_lt haq) he

/-- Positions outside the first pair have their partners outside too. -/
theorem partner_outside_first (p : NoncrossingPairing (n + 2)) (a : Fin (n + 2))
    (haq : p.partner 0 < a) : p.partner 0 < p.partner a := by
  have hne0 : p.partner a ≠ 0 := by
    intro h
    have he : a = p.partner 0 := by simpa using congrArg p.partner h
    exact (ne_of_gt haq) he
  have hneq : p.partner a ≠ p.partner 0 := by
    intro h
    have he : a = 0 := by simpa using congrArg p.partner h
    have : 0 < a := lt_of_le_of_lt (Fin.zero_le _) haq
    exact (ne_of_gt this) he
  by_contra h
  have hinside : p.partner a < p.partner 0 := lt_of_le_of_ne (le_of_not_gt h) hneq
  have hp0 : 0 < p.partner a := by
    change 0 < (p.partner a).val
    exact Nat.pos_of_ne_zero (fun h => hne0 (Fin.ext h))
  have hbound := (p.partner_inside_first (p.partner a) hp0 hinside).2
  rw [partner_partner] at hbound
  exact (not_lt_of_gt haq) hbound

/-- Number of positions inside the first pair. -/
noncomputable def firstSplitIndex (p : NoncrossingPairing (n + 2)) : Fin (n + 1) :=
  ⟨(p.partner 0).val - 1, by have h := (p.partner 0).isLt; omega⟩

theorem partner_zero_val (p : NoncrossingPairing (n + 2)) :
    (p.partner 0).val = (firstSplitIndex p).val + 1 := by
  have h := p.partner_ne 0
  have hp : (p.partner 0).val ≠ 0 := by
    intro he
    apply h
    exact Fin.ext he
  simp only [firstSplitIndex]
  omega

/-- Increasing inclusion of the interior interval. -/
def insideEmbedding (k : Fin (n + 1)) : Fin k.val ↪o Fin (n + 2) :=
  OrderEmbedding.ofStrictMono (fun a => ⟨a.val + 1, by have := a.isLt; have := k.isLt; omega⟩)
    (by intro a b hab; change a.val + 1 < b.val + 1; exact Nat.add_lt_add_right hab 1)

/-- Increasing inclusion of the exterior interval. -/
def outsideEmbedding (k : Fin (n + 1)) : Fin (n - k.val) ↪o Fin (n + 2) :=
  OrderEmbedding.ofStrictMono (fun a => ⟨k.val + 2 + a.val, by have := a.isLt; have := k.isLt; omega⟩)
    (by intro a b hab; change k.val + 2 + a.val < k.val + 2 + b.val; omega)

@[simp] theorem insideEmbedding_val (k : Fin (n + 1)) (a : Fin k.val) :
    (insideEmbedding k a).val = a.val + 1 := rfl

@[simp] theorem outsideEmbedding_val (k : Fin (n + 1)) (a : Fin (n - k.val)) :
    (outsideEmbedding k a).val = k.val + 2 + a.val := rfl

/-- The range of the interior inclusion is exactly the open interval inside the first pair. -/
theorem mem_range_insideEmbedding (k : Fin (n + 1)) (a : Fin (n + 2)) :
    a ∈ Set.range (insideEmbedding k) ↔ 0 < a.val ∧ a.val < k.val + 1 := by
  constructor
  · rintro ⟨b, rfl⟩
    simp only [insideEmbedding_val]
    have := b.isLt
    omega
  · rintro ⟨ha0, hak⟩
    refine ⟨⟨a.val - 1, by omega⟩, ?_⟩
    apply Fin.ext
    simp only [insideEmbedding_val]
    omega

/-- The exterior inclusion covers exactly the positions after the first pair's partner. -/
theorem mem_range_outsideEmbedding (k : Fin (n + 1)) (a : Fin (n + 2)) :
    a ∈ Set.range (outsideEmbedding k) ↔ k.val + 1 < a.val := by
  constructor
  · rintro ⟨b, rfl⟩
    simp only [outsideEmbedding_val]
    omega
  · intro ha
    refine ⟨⟨a.val - (k.val + 2), by have := a.isLt; have := k.isLt; omega⟩, ?_⟩
    apply Fin.ext
    simp only [outsideEmbedding_val]
    omega

theorem partner_mem_range_inside (p : NoncrossingPairing (n + 2))
    (a : Fin (firstSplitIndex p).val) :
    p.partner (insideEmbedding (firstSplitIndex p) a) ∈
      Set.range (insideEmbedding (firstSplitIndex p)) := by
  rw [mem_range_insideEmbedding]
  have h0 : 0 < insideEmbedding (firstSplitIndex p) a := by
    change 0 < a.val + 1
    omega
  have hq : insideEmbedding (firstSplitIndex p) a < p.partner 0 := by
    change a.val + 1 < (p.partner 0).val
    rw [partner_zero_val]
    exact Nat.add_lt_add_right a.isLt 1
  have h := p.partner_inside_first _ h0 hq
  simpa only [Fin.lt_def, Fin.val_zero, partner_zero_val] using h

theorem partner_mem_range_outside (p : NoncrossingPairing (n + 2))
    (a : Fin (n - (firstSplitIndex p).val)) :
    p.partner (outsideEmbedding (firstSplitIndex p) a) ∈
      Set.range (outsideEmbedding (firstSplitIndex p)) := by
  rw [mem_range_outsideEmbedding]
  have hq : p.partner 0 < outsideEmbedding (firstSplitIndex p) a := by
    change (p.partner 0).val < (firstSplitIndex p).val + 2 + a.val
    rw [partner_zero_val]
    omega
  have h := p.partner_outside_first _ hq
  simpa only [Fin.lt_def, partner_zero_val] using h

/-- The pairing carried by the interior of the first pair. -/
noncomputable def insidePairing (p : NoncrossingPairing (n + 2)) :
    NoncrossingPairing (firstSplitIndex p).val :=
  ⟨p.val.restrict (insideEmbedding (firstSplitIndex p)),
    p.isPairing_restrict _ (partner_mem_range_inside p)⟩

/-- The pairing carried by the exterior of the first pair. -/
noncomputable def outsidePairing (p : NoncrossingPairing (n + 2)) :
    NoncrossingPairing (n - (firstSplitIndex p).val) :=
  ⟨p.val.restrict (outsideEmbedding (firstSplitIndex p)),
    p.isPairing_restrict _ (partner_mem_range_outside p)⟩

/-- First-partner decomposition into the interior and exterior pairings. -/
noncomputable def firstDecomposition (p : NoncrossingPairing (n + 2)) :
    Σ k : Fin (n + 1), NoncrossingPairing k.val × NoncrossingPairing (n - k.val) :=
  ⟨firstSplitIndex p, insidePairing p, outsidePairing p⟩

/-- Equivalence relation induced by an involution: its classes are involution orbits. -/
def involutionSetoid (f : Fin n → Fin n) (hinv : Function.Involutive f) : Setoid (Fin n) where
  r a b := b = a ∨ b = f a
  iseqv := ⟨fun a => Or.inl rfl, by
    intro a b h
    rcases h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (hinv a).symm, by
    intro a b c hab hbc
    rcases hab with rfl | rfl
    · exact hbc
    · rcases hbc with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl (hinv a)⟩

/-- A fixed-point-free noncrossing involution gives an actual two-element-block partition. -/
def pairingOfInvolution (f : Fin n → Fin n) (hinv : Function.Involutive f)
    (hne : ∀ a, f a ≠ a) (hnc : IsNoncrossing (involutionSetoid f hinv)) :
    NoncrossingPairing n := by
  classical
  let p : NoncrossingPartition n := ⟨involutionSetoid f hinv, hnc⟩
  refine ⟨p, ?_⟩
  intro s hs
  obtain ⟨a, ha⟩ := p.block_nonempty hs
  have he : s = {a, f a} := by
    ext b
    rw [← p.rel_iff_mem_block hs ha b]
    change (b = a ∨ b = f a) ↔ b ∈ ({a, f a} : Finset (Fin n))
    simp
  rw [he]
  simp [Ne.symm (hne a)]

/-- The endpoint paired with zero for a specified interior size. -/
def splitPartner (k : Fin (n + 1)) : Fin (n + 2) :=
  ⟨k.val + 1, by have := k.isLt; omega⟩

@[simp] theorem splitPartner_val (k : Fin (n + 1)) : (splitPartner k).val = k.val + 1 := rfl

/-- Piecewise partner map for gluing an outer pair and its two interval pairings. -/
noncomputable def gluedPartner (k : Fin (n + 1)) (L : NoncrossingPairing k.val)
    (R : NoncrossingPairing (n - k.val)) (a : Fin (n + 2)) : Fin (n + 2) :=
  if h0 : a.val = 0 then splitPartner k
  else if hq : a.val = k.val + 1 then 0
  else if hi : a.val < k.val + 1 then
    insideEmbedding k (L.partner ⟨a.val - 1, by omega⟩)
  else
    outsideEmbedding k (R.partner ⟨a.val - (k.val + 2), by have := a.isLt; have := k.isLt; omega⟩)

@[simp] theorem gluedPartner_zero (k : Fin (n + 1)) (L : NoncrossingPairing k.val)
    (R : NoncrossingPairing (n - k.val)) : gluedPartner k L R 0 = splitPartner k := by
  simp [gluedPartner]

@[simp] theorem gluedPartner_splitPartner (k : Fin (n + 1)) (L : NoncrossingPairing k.val)
    (R : NoncrossingPairing (n - k.val)) : gluedPartner k L R (splitPartner k) = 0 := by
  simp [gluedPartner]

@[simp] theorem gluedPartner_inside (k : Fin (n + 1)) (L : NoncrossingPairing k.val)
    (R : NoncrossingPairing (n - k.val)) (a : Fin k.val) :
    gluedPartner k L R (insideEmbedding k a) = insideEmbedding k (L.partner a) := by
  have ha := a.isLt
  have hne : a.val ≠ k.val := ne_of_lt ha
  simp [gluedPartner, ha, hne]

@[simp] theorem gluedPartner_outside (k : Fin (n + 1)) (L : NoncrossingPairing k.val)
    (R : NoncrossingPairing (n - k.val)) (a : Fin (n - k.val)) :
    gluedPartner k L R (outsideEmbedding k a) = outsideEmbedding k (R.partner a) := by
  have hq : k.val + 2 + a.val ≠ k.val + 1 := by omega
  have hi : ¬k.val + 2 + a.val < k.val + 1 := by omega
  simp [gluedPartner, hq, hi]

/-- Every position lies in exactly one of the four pieces used for gluing. -/
theorem splitPosition_cases (k : Fin (n + 1)) (a : Fin (n + 2)) :
    a = 0 ∨ a = splitPartner k ∨
      a ∈ Set.range (insideEmbedding k) ∨ a ∈ Set.range (outsideEmbedding k) := by
  by_cases h0 : a.val = 0
  · exact Or.inl (Fin.ext h0)
  · by_cases hq : a.val = k.val + 1
    · exact Or.inr (Or.inl (Fin.ext hq))
    · by_cases hi : a.val < k.val + 1
      · exact Or.inr (Or.inr (Or.inl ((mem_range_insideEmbedding k a).mpr ⟨by omega, hi⟩)))
      · exact Or.inr (Or.inr (Or.inr ((mem_range_outsideEmbedding k a).mpr (by omega))))

/-- The glued partner map is genuinely involutive. -/
theorem gluedPartner_involutive (k : Fin (n + 1)) (L : NoncrossingPairing k.val)
    (R : NoncrossingPairing (n - k.val)) : Function.Involutive (gluedPartner k L R) := by
  intro a
  rcases splitPosition_cases k a with rfl | rfl | ⟨b, rfl⟩ | ⟨b, rfl⟩ <;> simp

/-- No position is fixed by the glued partner map. -/
theorem gluedPartner_ne (k : Fin (n + 1)) (L : NoncrossingPairing k.val)
    (R : NoncrossingPairing (n - k.val)) (a : Fin (n + 2)) : gluedPartner k L R a ≠ a := by
  rcases splitPosition_cases k a with rfl | rfl | ⟨b, rfl⟩ | ⟨b, rfl⟩
  · simp only [gluedPartner_zero]
    intro h
    have hv := congrArg Fin.val h
    simp only [splitPartner_val, Fin.val_zero] at hv
    omega
  · simp only [gluedPartner_splitPartner]
    intro h
    have hv := congrArg Fin.val h
    simp only [splitPartner_val, Fin.val_zero] at hv
    omega
  · simp only [gluedPartner_inside]
    exact fun h => L.partner_ne b ((insideEmbedding k).injective h)
  · simp only [gluedPartner_outside]
    exact fun h => R.partner_ne b ((outsideEmbedding k).injective h)

/-- Distinct pairs of a noncrossing pairing cannot interlace. -/
theorem not_interlaced_partners (p : NoncrossingPairing n) (a b : Fin n)
    (hab : a < b) (hbc : b < p.partner a) (hcd : p.partner a < p.partner b) : False := by
  have hr := p.val.property a b (p.partner a) (p.partner b) hab hbc hcd
    (p.rel_partner a) (p.rel_partner b)
  rcases (p.rel_iff a b).mp hr with he | he
  · exact (ne_of_gt hab) he
  · exact (ne_of_lt hbc) he

/-- The glued orbit relation is noncrossing; interval separation forbids mixed-region crossings. -/
theorem gluedPartner_isNoncrossing (k : Fin (n + 1)) (L : NoncrossingPairing k.val)
    (R : NoncrossingPairing (n - k.val)) :
    IsNoncrossing (involutionSetoid (gluedPartner k L R) (gluedPartner_involutive k L R)) := by
  intro a b c d hab hbc hcd hac hbd
  have hc : c = gluedPartner k L R a := hac.resolve_left (ne_of_gt (lt_trans hab hbc))
  have hd : d = gluedPartner k L R b := hbd.resolve_left (ne_of_gt (lt_trans hbc hcd))
  subst c d
  exfalso
  rcases splitPosition_cases k a with rfl | rfl | ⟨a, rfl⟩ | ⟨a, rfl⟩
  · simp only [gluedPartner_zero] at hbc hcd
    have hb : b ∈ Set.range (insideEmbedding k) := by
      rw [mem_range_insideEmbedding]
      exact ⟨by simpa only [Fin.lt_def, Fin.val_zero] using hab,
        by simpa only [Fin.lt_def, splitPartner_val] using hbc⟩
    obtain ⟨b, rfl⟩ := hb
    rw [gluedPartner_inside] at hcd
    have hlt : insideEmbedding k (L.partner b) < splitPartner k := by
      change (L.partner b).val + 1 < k.val + 1
      exact Nat.add_lt_add_right (L.partner b).isLt 1
    exact (not_lt_of_gt hlt) hcd
  · rw [gluedPartner_splitPartner] at hbc
    exact (not_lt_of_ge (Fin.zero_le _)) (lt_trans hab hbc)
  · rw [gluedPartner_inside] at hbc hcd
    have ha0 : 0 < insideEmbedding k a := by change 0 < a.val + 1; omega
    have hq : insideEmbedding k (L.partner a) < splitPartner k := by
      change (L.partner a).val + 1 < k.val + 1
      exact Nat.add_lt_add_right (L.partner a).isLt 1
    have hb : b ∈ Set.range (insideEmbedding k) := by
      rw [mem_range_insideEmbedding]
      exact ⟨by simpa only [Fin.lt_def, Fin.val_zero] using lt_trans ha0 hab,
        by simpa only [Fin.lt_def, splitPartner_val] using lt_trans hbc hq⟩
    obtain ⟨b, rfl⟩ := hb
    rw [gluedPartner_inside] at hcd
    exact L.not_interlaced_partners a b ((insideEmbedding k).lt_iff_lt.mp hab)
      ((insideEmbedding k).lt_iff_lt.mp hbc) ((insideEmbedding k).lt_iff_lt.mp hcd)
  · rw [gluedPartner_outside] at hbc hcd
    have hb : b ∈ Set.range (outsideEmbedding k) := by
      rw [mem_range_outsideEmbedding]
      have hv : k.val + 2 + a.val < b.val := hab
      omega
    obtain ⟨b, rfl⟩ := hb
    rw [gluedPartner_outside] at hcd
    exact R.not_interlaced_partners a b ((outsideEmbedding k).lt_iff_lt.mp hab)
      ((outsideEmbedding k).lt_iff_lt.mp hbc) ((outsideEmbedding k).lt_iff_lt.mp hcd)

/-- Glue an outer pair around an interior pairing, followed by an exterior pairing. -/
noncomputable def glue (k : Fin (n + 1)) (L : NoncrossingPairing k.val)
    (R : NoncrossingPairing (n - k.val)) : NoncrossingPairing (n + 2) :=
  pairingOfInvolution (gluedPartner k L R) (gluedPartner_involutive k L R)
    (gluedPartner_ne k L R) (gluedPartner_isNoncrossing k L R)

/-- The constructor's partner map is exactly the supplied involution. -/
theorem partner_pairingOfInvolution (f : Fin n → Fin n) (hinv : Function.Involutive f)
    (hne : ∀ a, f a ≠ a) (hnc : IsNoncrossing (involutionSetoid f hinv)) (a : Fin n) :
    (pairingOfInvolution f hinv hne hnc).partner a = f a := by
  have hr : (pairingOfInvolution f hinv hne hnc).val.val.r a (f a) := Or.inr rfl
  exact (((pairingOfInvolution f hinv hne hnc).rel_iff a (f a)).mp hr).resolve_left (hne a) |>.symm

@[simp] theorem partner_glue (k : Fin (n + 1)) (L : NoncrossingPairing k.val)
    (R : NoncrossingPairing (n - k.val)) (a : Fin (n + 2)) :
    (glue k L R).partner a = gluedPartner k L R a :=
  partner_pairingOfInvolution _ _ _ _ _

@[simp] theorem firstSplitIndex_glue (k : Fin (n + 1)) (L : NoncrossingPairing k.val)
    (R : NoncrossingPairing (n - k.val)) : firstSplitIndex (glue k L R) = k := by
  apply Fin.ext
  simp [firstSplitIndex]

/-- Gluing and then restricting the interior restores the interior partition. -/
theorem restrict_glue_inside (k : Fin (n + 1)) (L : NoncrossingPairing k.val)
    (R : NoncrossingPairing (n - k.val)) :
    (glue k L R).val.restrict (insideEmbedding k) = L.val := by
  apply Subtype.ext
  apply Setoid.ext
  intro a b
  change (glue k L R).val.val.r (insideEmbedding k a) (insideEmbedding k b) ↔ L.val.val.r a b
  rw [(glue k L R).rel_iff, L.rel_iff, partner_glue, gluedPartner_inside]
  simp only [(insideEmbedding k).injective.eq_iff]

/-- Gluing and then restricting the exterior restores the exterior partition. -/
theorem restrict_glue_outside (k : Fin (n + 1)) (L : NoncrossingPairing k.val)
    (R : NoncrossingPairing (n - k.val)) :
    (glue k L R).val.restrict (outsideEmbedding k) = R.val := by
  apply Subtype.ext
  apply Setoid.ext
  intro a b
  change (glue k L R).val.val.r (outsideEmbedding k a) (outsideEmbedding k b) ↔ R.val.val.r a b
  rw [(glue k L R).rel_iff, R.rel_iff, partner_glue, gluedPartner_outside]
  simp only [(outsideEmbedding k).injective.eq_iff]

/-- A pairing is uniquely determined by its partner involution. -/
theorem eq_of_partner_eq (p q : NoncrossingPairing n) (h : ∀ a, p.partner a = q.partner a) : p = q := by
  apply Subtype.ext
  apply Subtype.ext
  apply Setoid.ext
  intro a b
  rw [p.rel_iff, q.rel_iff, h a]

/-- Partner maps of restricted pairings transport through the ordered inclusion. -/
theorem partner_restrict_map (p : NoncrossingPairing n) (f : Fin m ↪o Fin n)
    (hp : (p.val.restrict f).IsPairing) (a : Fin m) :
    f (partner (⟨p.val.restrict f, hp⟩ : NoncrossingPairing m) a) = p.partner (f a) := by
  let q : NoncrossingPairing m := ⟨p.val.restrict f, hp⟩
  have hr : p.val.val.r (f a) (f (q.partner a)) := q.rel_partner a
  have hne : f (q.partner a) ≠ f a := fun h => q.partner_ne a (f.injective h)
  exact ((p.rel_iff (f a) (f (q.partner a))).mp hr).resolve_left hne

@[simp] theorem splitPartner_firstSplitIndex (p : NoncrossingPairing (n + 2)) :
    splitPartner (firstSplitIndex p) = p.partner 0 :=
  Fin.ext (partner_zero_val p).symm

/-- Splitting and gluing restores the entire original pairing. -/
theorem glue_firstDecomposition (p : NoncrossingPairing (n + 2)) :
    glue (firstSplitIndex p) (insidePairing p) (outsidePairing p) = p := by
  apply eq_of_partner_eq
  intro a
  rw [partner_glue]
  rcases splitPosition_cases (firstSplitIndex p) a with rfl | rfl | ⟨b, rfl⟩ | ⟨b, rfl⟩
  · simp
  · rw [gluedPartner_splitPartner, splitPartner_firstSplitIndex, partner_partner]
  · rw [gluedPartner_inside]
    exact partner_restrict_map p (insideEmbedding (firstSplitIndex p)) _ b
  · rw [gluedPartner_outside]
    exact partner_restrict_map p (outsideEmbedding (firstSplitIndex p)) _ b

/-- Transport the interior pairing to an explicitly identified size index. -/
noncomputable def insideAt (p : NoncrossingPairing (n + 2)) (k : Fin (n + 1))
    (h : firstSplitIndex p = k) : NoncrossingPairing k.val := h ▸ insidePairing p

/-- Transport the exterior pairing to an explicitly identified size index. -/
noncomputable def outsideAt (p : NoncrossingPairing (n + 2)) (k : Fin (n + 1))
    (h : firstSplitIndex p = k) : NoncrossingPairing (n - k.val) := h ▸ outsidePairing p

theorem insideAt_val (p : NoncrossingPairing (n + 2)) (k : Fin (n + 1))
    (h : firstSplitIndex p = k) : (insideAt p k h).val = p.val.restrict (insideEmbedding k) := by
  subst k
  rfl

theorem outsideAt_val (p : NoncrossingPairing (n + 2)) (k : Fin (n + 1))
    (h : firstSplitIndex p = k) : (outsideAt p k h).val = p.val.restrict (outsideEmbedding k) := by
  subst k
  rfl

theorem firstDecomposition_eq_at (p : NoncrossingPairing (n + 2)) (k : Fin (n + 1))
    (h : firstSplitIndex p = k) : firstDecomposition p = ⟨k, insideAt p k h, outsideAt p k h⟩ := by
  subst k
  rfl

/-- Gluing and splitting restores both interval pairings and their size index. -/
theorem firstDecomposition_glue (k : Fin (n + 1)) (L : NoncrossingPairing k.val)
    (R : NoncrossingPairing (n - k.val)) : firstDecomposition (glue k L R) = ⟨k, L, R⟩ := by
  rw [firstDecomposition_eq_at (glue k L R) k (firstSplitIndex_glue k L R)]
  have hi : insideAt (glue k L R) k (firstSplitIndex_glue k L R) = L := by
    apply Subtype.ext
    rw [insideAt_val, restrict_glue_inside]
  have ho : outsideAt (glue k L R) k (firstSplitIndex_glue k L R) = R := by
    apply Subtype.ext
    rw [outsideAt_val, restrict_glue_outside]
  rw [hi, ho]

/-- First-partner splitting is a genuine equivalence of actual noncrossing pairings. -/
noncomputable def firstPartnerEquiv (n : ℕ) : NoncrossingPairing (n + 2) ≃
    Σ k : Fin (n + 1), NoncrossingPairing k.val × NoncrossingPairing (n - k.val) where
  toFun := firstDecomposition
  invFun x := glue x.1 x.2.1 x.2.2
  left_inv := glue_firstDecomposition
  right_inv x := by obtain ⟨k, L, R⟩ := x; exact firstDecomposition_glue k L R

end FreeProbability.NoncrossingPairing

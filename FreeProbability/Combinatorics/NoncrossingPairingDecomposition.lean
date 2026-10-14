import FreeProbability.Combinatorics.NoncrossingPairing
import FreeProbability.Combinatorics.NoncrossingRestriction

/-!
# Decomposition of noncrossing pairings at the partner of zero

The partner of the first position separates two invariant ordered intervals.
Restriction to either interval remains a genuine pairing. The inverse gluing
and the resulting first-partner equivalence are developed subsequently.
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

/-- Forward first-partner decomposition; inverse gluing remains to establish the equivalence. -/
noncomputable def firstDecomposition (p : NoncrossingPairing (n + 2)) :
    Σ k : Fin (n + 1), NoncrossingPairing k.val × NoncrossingPairing (n - k.val) :=
  ⟨firstSplitIndex p, insidePairing p, outsidePairing p⟩

end FreeProbability.NoncrossingPairing


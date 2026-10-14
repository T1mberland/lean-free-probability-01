import FreeProbability.Combinatorics.NoncrossingInterval

/-! # Adjacent-pair or noninitial-singleton reduction of noncrossing partitions -/

namespace FreeProbability.NoncrossingPartition

variable {n : ℕ}

/-- Every partition on at least two positions either has an adjacent pair in
one block or a singleton away from the initial position. This avoids a cyclic
boundary case in deletion induction. -/
theorem exists_adjacent_or_singleton_succ (p : NoncrossingPartition (n + 1)) (hn : 0 < n) :
    (∃ i : Fin n, p.val.r i.castSucc i.succ) ∨
      (∃ i : Fin n, ∀ j, p.val.r i.succ j → j = i.succ) := by
  classical
  by_cases hadj : ∃ i : Fin n, p.val.r i.castSucc i.succ
  · exact Or.inl hadj
  right
  have hno : ∀ i : Fin n, ¬ p.val.r i.castSucc i.succ := by
    intro i hi
    exact hadj ⟨i, hi⟩
  have hb : ∃ b : Fin (n + 1), ¬ p.val.r 0 b := by
    by_contra h
    push Not at h
    exact hno ⟨0, hn⟩ (h ⟨1, by omega⟩)
  obtain ⟨b, hb⟩ := hb
  obtain ⟨j, hjb, hj⟩ := p.exists_least_representative b
  have hjpos : 0 < j.val := by
    by_contra h
    have he : j = 0 := by
      apply Fin.ext
      change j.val = 0
      omega
    exact hb (he ▸ hjb)
  let reps : Finset (Fin (n + 1)) := Finset.univ.filter
    (fun i => ∀ k, p.val.r i k → i ≤ k)
  have hjmem : j ∈ reps := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
  have hreps : reps.Nonempty := ⟨j, hjmem⟩
  let a := reps.max' hreps
  have ha : ∀ k, p.val.r a k → a ≤ k :=
    (Finset.mem_filter.mp (Finset.max'_mem reps hreps)).2
  have haj : j ≤ a := Finset.le_max' reps j hjmem
  have hapos : 0 < a.val := by
    have : j.val ≤ a.val := haj
    omega
  have hsingle : ∀ k, p.val.r a k → k = a := by
    intro k hak
    by_contra hne
    have haklt : a < k := lt_of_le_of_ne (ha k hak) (Ne.symm hne)
    have haval : a.val < k.val := haklt
    let i : Fin n := ⟨a.val, by omega⟩
    have haeq : i.castSucc = a := Fin.ext rfl
    have hil : a < i.succ := by
      change a.val < a.val + 1
      omega
    have hlk : i.succ ≤ k := by
      change a.val + 1 ≤ k.val
      omega
    have hnot : ¬ p.val.r a i.succ := by simpa only [haeq] using hno i
    rcases eq_or_lt_of_le hlk with heq | hlt
    · exact hnot (heq.symm ▸ hak)
    obtain ⟨c, hcl, hc⟩ := p.exists_least_representative i.succ
    have hca : c ≤ a := Finset.le_max' reps c
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
    rcases eq_or_lt_of_le hca with heq | hltca
    · exact hnot (heq ▸ hcl)
    have hrel : p.val.r c a := p.property c a i.succ k hltca hil hlt hcl hak
    exact hnot (p.val.trans (p.val.symm hrel) hcl)
  let i : Fin n := ⟨a.val - 1, by omega⟩
  have hi : i.succ = a := by
    apply Fin.ext
    change a.val - 1 + 1 = a.val
    omega
  exact ⟨i, fun k hk => by rw [hi] at hk ⊢; exact hsingle k hk⟩

end FreeProbability.NoncrossingPartition

import FreeProbability

/-! Small applications of the public interfaces, checked with the audit target. -/

namespace FreeProbability.Examples

/-- An odd-order pairing sum is zero for every choice of weights. This is the
combinatorial side of the vanishing of odd moments in a Wick formula. -/
example {n : ℕ} (hn : Odd n) (weight : NoncrossingPairing n → ℂ) :
    ∑ p, weight p = 0 := by
  classical
  letI : IsEmpty (NoncrossingPairing n) :=
    ⟨fun p => NoncrossingPairing.not_nonempty_of_odd hn ⟨p⟩⟩
  simp

/-- The adjacent-pair theorem expressed using the public partner map. -/
example {n : ℕ} (p : NoncrossingPairing n) (hn : 0 < n) :
    ∃ i : Fin n, i.val + 1 = (p.partner i).val := by
  obtain ⟨i, j, hij, hrel⟩ := p.property.exists_adjacent hn
  have hji : j ≠ i := by
    intro h
    subst j
    omega
  have hj := (p.rel_iff i j).mp hrel
  exact ⟨i, (hj.resolve_left hji) ▸ hij⟩

end FreeProbability.Examples

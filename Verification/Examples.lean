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

end FreeProbability.Examples

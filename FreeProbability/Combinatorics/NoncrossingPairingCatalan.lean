import FreeProbability.Combinatorics.NoncrossingPairingWeights
import Mathlib.Combinatorics.Enumerative.Catalan.Basic

/-! # Actual noncrossing pairings are counted by Catalan numbers -/

noncomputable section
open scoped Classical BigOperators

namespace FreeProbability.NoncrossingPairing

/-- The number of actual pairings of `2n` positions is the `n`th Catalan number. -/
theorem card_even_eq_catalan (n : ℕ) : Fintype.card (NoncrossingPairing (2 * n)) = catalan n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [card_even_convolution, catalan_succ]
      apply Finset.sum_congr rfl
      intro k hk
      rw [ih k.val k.isLt, ih (n - k.val) (by omega)]

/-- Complete cardinal formula, with the odd obstruction kept explicit. -/
theorem card_eq_catalan_or_zero (n : ℕ) : Fintype.card (NoncrossingPairing n) =
    if Even n then catalan (n / 2) else 0 := by
  by_cases hn : Even n
  · obtain ⟨m, hm⟩ := hn
    have he : n = 2 * m := by omega
    rw [he]
    rw [card_even_eq_catalan]
    simp
  · simp [hn, card_eq_zero_of_odd (Nat.not_even_iff_odd.mp hn)]

end FreeProbability.NoncrossingPairing

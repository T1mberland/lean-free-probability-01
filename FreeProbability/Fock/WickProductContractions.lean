import FreeProbability.Fock.WickProductWordAction
import FreeProbability.Fock.GeneratedState

/-!
# Actual Wick operator multiplication and reversed color contractions

The identity is an equality of actual bounded operators. The normal-order action
on the vacuum is promoted to operator equality by the proved separating vacuum
property of the generated semicircular algebra.
-/

noncomputable section
open scoped Classical

namespace FreeProbability.Fock

variable {I : Type*}

/-- Actual Wick multiplication: every matching reversed suffix contracts against the second
word's prefix, and the remaining colors concatenate in their original order. -/
theorem wick_product_contractions (u v : List I) :
    wick u * wick v = ∑ k : Fin (u.length + 1),
      if (u.drop k.val).reverse.IsPrefix v then
        wick (u.take k.val ++ v.drop (u.length - k.val)) else 0 := by
  let T := wick u * wick v - ∑ k : Fin (u.length + 1),
    if (u.drop k.val).reverse.IsPrefix v then
      wick (u.take k.val ++ v.drop (u.length - k.val)) else 0
  have hT : T ∈ semicircularAlgebra I := by
    apply (semicircularAlgebra I).sub_mem
      ((semicircularAlgebra I).mul_mem (wick_mem_algebra u) (wick_mem_algebra v))
    apply (semicircularAlgebra I).sum_mem
    intro k hk
    split
    · exact wick_mem_algebra _
    · exact (semicircularAlgebra I).zero_mem
  have hΩ : T (vacuum : WordSpace I) = 0 := by
    change (wick u * wick v) vacuum - (∑ k : Fin (u.length + 1),
      if (u.drop k.val).reverse.IsPrefix v then
        wick (u.take k.val ++ v.drop (u.length - k.val)) else 0) vacuum = 0
    rw [mul_apply_eq_comp, wick_vacuum, wick_word_action_cuts, sub_eq_zero]
    rw [sum_apply]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases h : (u.drop k.val).reverse.IsPrefix v <;> simp [h]
  have he := eq_zero_of_commute_right_of_vacuum_eq_zero T
    (commute_right_of_mem_semicircularAlgebra hT) hΩ
  exact sub_eq_zero.mp he

end FreeProbability.Fock

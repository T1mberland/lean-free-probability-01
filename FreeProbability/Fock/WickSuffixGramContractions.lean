import FreeProbability.Fock.WickProductContractions
import FreeProbability.Fock.WordVonNeumannTrace

/-! # Actual adjoint Wick operators and the suffix contraction starting point -/
noncomputable section
open scoped Classical
namespace FreeProbability.Fock
variable {I : Type*}

/-- The actual bounded Wick adjoint reverses the word, on the entire completed space. -/
theorem star_wick (w : List I) : star (wick w) = wick w.reverse := by
  let T := star (wick w) - wick w.reverse
  have hs : star (wick w) ∈ semicircularAlgebra I := star_mem (wick_mem_algebra w)
  have hm : T ∈ semicircularAlgebra I :=
    (semicircularAlgebra I).sub_mem hs
      (wick_mem_algebra w.reverse)
  have hv : T (vacuum : WordSpace I) = 0 := by
    change star (wick w) vacuum - wick w.reverse vacuum = 0
    rw [star_wick_vacuum, wick_vacuum, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_commute_right_of_vacuum_eq_zero T
    (commute_right_of_mem_semicircularAlgebra hm) hv)

/-- Actual bounded-operator contraction expansion with the second factor adjointed.
The reversed-prefix condition encodes a common suffix; no scalar commutation is used. -/
theorem wick_mul_star_contractions (u v : List I) :
    wick u * star (wick v) = ∑ k : Fin (u.length + 1),
      if (u.drop k.val).reverse.IsPrefix v.reverse then
        wick (u.take k.val ++ v.reverse.drop (u.length - k.val)) else 0 := by
  rw [star_wick]
  exact wick_product_contractions u v.reverse

/-- Common-suffix form of the actual Wick product. Each surviving cut removes
exactly the same terminal letters from both factors. -/
theorem wick_mul_star_common_suffix (u v : List I) :
    wick u * star (wick v) = ∑ k : Fin (u.length + 1),
      if (u.drop k.val).IsSuffix v then
        wick (u.take k.val ++ (v.take (v.length - (u.length - k.val))).reverse) else 0 := by
  rw [wick_mul_star_contractions]
  simp only [List.reverse_prefix, List.drop_reverse]

end FreeProbability.Fock

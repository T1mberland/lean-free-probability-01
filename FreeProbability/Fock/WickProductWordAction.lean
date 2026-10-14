import FreeProbability.Fock.WickProductNormalOrder
import Mathlib.Data.List.Infix

/-! # Exact Wick action and reversed color overlap on the actual orthonormal word basis -/

noncomputable section
open scoped Classical

namespace FreeProbability.Fock

variable {I : Type*}

@[simp] theorem creationWord_append (u v : List I) :
    creationWord (u ++ v) = creationWord u * creationWord v := by
  simp only [creationWord, List.map_append, List.prod_append]

@[simp] theorem annihilationWord_append (u v : List I) :
    annihilationWord (u ++ v) = annihilationWord u * annihilationWord v := by
  simp only [annihilationWord, List.map_append, List.prod_append]

/-- Ordered creators concatenate the exact original color word. -/
theorem creationWord_word (u v : List I) : creationWord u (word v) = word (u ++ v) := by
  induction u with
  | nil => simp
  | cons i u ih => simp [mul_apply_eq_comp, ih]

/-- Reversely ordered annihilation removes precisely a matching prefix of colors. -/
theorem annihilationWord_reverse_word (u v : List I) :
    annihilationWord u.reverse (word v) =
      if u.IsPrefix v then word (v.drop u.length) else 0 := by
  induction u generalizing v with
  | nil => simp
  | cons i u ih =>
    cases v with
    | nil =>
      simp [List.reverse_cons, mul_apply_eq_comp, annihilationWord_append,
        annihilationWord_cons]
    | cons j v =>
      simp only [List.reverse_cons, annihilationWord_append, annihilationWord_cons,
        annihilationWord_nil, mul_one, mul_apply_eq_comp, annihilation_word,
        List.length_cons, List.drop_succ_cons, List.cons_prefix_cons]
      by_cases h : i = j
      · subst j
        simp [ih]
      · simp [h]

/-- The original annihilator order removes a prefix matching its reverse, and nothing else. -/
theorem annihilationWord_word (u v : List I) :
    annihilationWord u (word v) =
      if u.reverse.IsPrefix v then word (v.drop u.length) else 0 := by
  simpa only [List.reverse_reverse, List.length_reverse] using
    annihilationWord_reverse_word u.reverse v

/-- Every normal-order cut acts by an exact reversed-suffix color contraction. -/
theorem wick_word_action_cuts (u v : List I) :
    wick u (word v) = ∑ k : Fin (u.length + 1),
      if (u.drop k.val).reverse.IsPrefix v then
        word (u.take k.val ++ v.drop (u.length - k.val)) else 0 := by
  rw [wick_normal_order_expansion]
  simp only [sum_apply, mul_apply_eq_comp]
  apply Finset.sum_congr rfl
  intro k hk
  rw [annihilationWord_word]
  by_cases h : (u.drop k.val).reverse.IsPrefix v
  · simp only [h, ite_true, List.length_drop]
    exact creationWord_word _ _
  · simp [h]

end FreeProbability.Fock

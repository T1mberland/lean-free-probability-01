import FreeProbability.Fock.WordVonNeumann
import FreeProbability.Fock.WickProductWordAction

/-! # Actual reversed-adjoint Wick vacuum vectors -/
noncomputable section
open scoped Classical InnerProductSpace BigOperators
namespace FreeProbability.Fock
variable {I : Type*}

theorem star_creationWord (w : List I) : star (creationWord w) = annihilationWord w.reverse := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [creationWord_cons, star_mul, ih, List.reverse_cons, annihilationWord_append]
    simp only [annihilationWord_cons, annihilationWord_nil, mul_one]
    rfl

theorem star_annihilationWord (w : List I) : star (annihilationWord w) = creationWord w.reverse := by
  have h := congrArg star (star_creationWord w.reverse)
  simpa only [star_star, List.reverse_reverse] using h.symm

/-- The adjoint Wick polynomial sends the actual vacuum to the reversed word. -/
theorem star_wick_vacuum (w : List I) :
    star (wick w) (vacuum : WordSpace I) = word w.reverse := by
  cases w with
  | nil => simp [vacuum]
  | cons i w =>
    have hs : star (wick (i :: w)) =
        ∑ k : Fin ((i :: w).length + 1),
          star (creationWord ((i :: w).take k.val) * annihilationWord ((i :: w).drop k.val)) := by
      rw [wick_normal_order_expansion]
      exact star_sum (Finset.univ : Finset (Fin ((i :: w).length + 1)))
        (fun k : Fin ((i :: w).length + 1) =>
          creationWord ((i :: w).take k.val) * annihilationWord ((i :: w).drop k.val))
    rw [hs]
    simp only [star_mul, star_annihilationWord, star_creationWord, sum_apply, mul_apply_eq_comp]
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, List.take_zero, List.drop_zero,
      List.reverse_nil, annihilationWord_nil, List.take_succ_cons]
    have hz (k : Fin (w.length + 1)) :
        creationWord ((i :: w).drop (k.val + 1)).reverse
          (annihilationWord (i :: w.take k.val).reverse (vacuum : WordSpace I)) = 0 := by
      rw [show (vacuum : WordSpace I) = word [] from rfl, annihilationWord_reverse_word]
      simp
    simp only [hz, Finset.sum_const_zero, add_zero]
    change creationWord (i :: w).reverse (word []) = word (i :: w).reverse
    rw [creationWord_word, List.append_nil]

end FreeProbability.Fock

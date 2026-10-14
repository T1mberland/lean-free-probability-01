import FreeProbability.Fock.BoundaryCommutator
import Mathlib.Algebra.BigOperators.Fin

/-!
# Word integration by parts and the full joint moment recursion

The boundary commutator differentiates arbitrary finite products. Evaluating the
actual vacuum state yields the scalar free integration-by-parts identity on every
word. Identification of this recursion with the literal noncrossing-pairing sum
is a subsequent combinatorial theorem.
-/

noncomputable section
open scoped Classical BigOperators InnerProductSpace

namespace FreeProbability

/-- The commutator of a finite ordered product is the sum of its Leibniz insertions. -/
theorem commutator_list_prod {A : Type*} [Ring A] (C : A) (w : List A) :
    C * w.prod - w.prod * C =
      ∑ k : Fin w.length, (w.take k.val).prod *
        (C * w.get k - w.get k * C) * (w.drop (k.val + 1)).prod := by
  induction w with
  | nil => simp
  | cons a w ih =>
    simp only [List.length_cons]
    rw [List.prod_cons, Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, List.take_zero, List.prod_nil,
      List.get_cons_zero, List.drop_succ_cons, List.drop_zero,
      List.take_succ_cons, List.prod_cons, one_mul]
    have hs : (∑ k : Fin w.length, (a * (w.take k.val).prod) *
        (C * w.get k - w.get k * C) * (w.drop (k.val + 1)).prod) =
        a * (∑ k : Fin w.length, (w.take k.val).prod *
          (C * w.get k - w.get k * C) * (w.drop (k.val + 1)).prod) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      noncomm_ring
    simp only [List.get_eq_getElem, Fin.val_succ, List.getElem_cons_succ]
    simp only [List.get_eq_getElem] at hs ih
    rw [hs, ← ih]
    noncomm_ring

namespace Fock

variable {I : Type*}

/-- The ordered operator product of a color word. -/
def operatorWord (w : List I) : WordSpace I →L[ℂ] WordSpace I :=
  (w.map semicircular).prod

@[simp] theorem operatorWord_nil : operatorWord ([] : List I) = 1 := rfl

@[simp] theorem operatorWord_cons (i : I) (w : List I) :
    operatorWord (i :: w) = semicircular i * operatorWord w := rfl

/-- Vacuum evaluation of the commutator is the leading semicircular moment. -/
theorem vacuumExpectation_rightAnnihilation_commutator (i : I)
    (T : WordSpace I →L[ℂ] WordSpace I) :
    vacuumExpectation (rightAnnihilation i * T - T * rightAnnihilation i) =
      vacuumExpectation (semicircular i * T) := by
  change inner ℂ vacuum (rightAnnihilation i (T vacuum) - T (rightAnnihilation i vacuum)) =
    inner ℂ vacuum (semicircular i (T vacuum))
  rw [rightAnnihilation_vacuum, map_zero, sub_zero, rightAnnihilation,
    ContinuousLinearMap.adjoint_inner_right, rightCreation_vacuum]
  rw [← semicircular_vacuum i, ← ContinuousLinearMap.adjoint_inner_right, adjoint_semicircular]

/-- Exact free integration by parts on every word, equivalently the full joint moment recursion. -/
theorem vacuumExpectation_operatorWord_cons (i : I) (w : List I) :
    vacuumExpectation (operatorWord (i :: w)) =
      ∑ k : Fin w.length, if i = w.get k then
        vacuumExpectation (operatorWord (w.take k.val)) *
          vacuumExpectation (operatorWord (w.drop (k.val + 1))) else 0 := by
  rw [operatorWord_cons, ← vacuumExpectation_rightAnnihilation_commutator,
    operatorWord, commutator_list_prod]
  change vacuumLinear (∑ k : Fin (w.map semicircular).length, _) = _
  rw [map_sum]
  apply Fintype.sum_equiv (finCongr (List.length_map (as := w) semicircular))
  intro k
  simp only [← List.map_take, ← List.map_drop, List.get_eq_getElem, List.getElem_map]
  have hk : (finCongr (List.length_map (as := w) semicircular) k).val = k.val := rfl
  simp only [hk]
  rw [rightAnnihilation_semicircular_commutator]
  by_cases h : i = w[k.val]
  · simp only [h, ite_true]
    exact vacuumExpectation_mul_vacuumProjection_mul _ _
  · simp [h, vacuumLinear]

end Fock
end FreeProbability

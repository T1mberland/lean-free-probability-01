import FreeProbability.Combinatorics.ConsecutiveFusionRepresentation
import FreeProbability.Combinatorics.BlockAdjacentTransport

/-! # Pointwise products of consecutive interval fibers -/

namespace FreeProbability

/-- The ordered product of the original entries assigned to a final position. -/
noncomputable def intervalProducts {n m : ℕ} {A : Type*} [Monoid A]
    (f : Fin n → Fin m) (x : Fin n → A) (a : Fin m) : A :=
  (orderedBlockWord x (Finset.univ.filter (fun b => f b = a))).prod

/-- Adjacent fusion preserves the ordered product in each duplicated subset. -/
theorem orderedBlockWord_prod_fuseAdjacent {n : ℕ} {A : Type*} [Monoid A]
    (x : Fin (n + 1) → A) (i : Fin n) (s : Finset (Fin n)) :
    (orderedBlockWord (fuseAdjacent x i) s).prod =
      (orderedBlockWord x (NoncrossingPartition.duplicateBlock i s)).prod := by
  classical
  by_cases hi : i ∈ s
  · rw [← orderedBlockWord_fuseAdjacent_of_mem x i s hi, prod_ofFn_fuseAdjacent,
      orderedBlockWord_duplicateBlock_of_mem x i s hi]
  · rw [NoncrossingPartition.orderedBlockWord_duplicateBlock_of_not_mem x i s hi]

namespace ConsecutiveFusion

/-- Each final entry is exactly the sorted product over its original interval
fiber. This identifies the expression independently of the chosen fusion plan. -/
theorem applyWord_eq_intervalProducts {n m : ℕ} {A : Type*} [Monoid A]
    (t : ConsecutiveFusion n m) (x : Fin n → A) :
    t.applyWord x = intervalProducts t.quotient x := by
  classical
  induction t with
  | refl n =>
    funext a
    change x a = (orderedBlockWord x (Finset.univ.filter (fun b => b = a))).prod
    have he : Finset.univ.filter (fun b : Fin n => b = a) = {a} := by
      ext b
      simp
    rw [he]
    simp [orderedBlockWord]
  | cons i t ih =>
    funext a
    change t.applyWord (fuseAdjacent x i) a = _
    rw [ih]
    unfold intervalProducts
    rw [orderedBlockWord_prod_fuseAdjacent]
    congr 2
    ext b
    rw [NoncrossingPartition.mem_duplicateBlock]
    change i.predAbove b ∈ Finset.univ.filter (fun c => t.quotient c = a) ↔
      b ∈ Finset.univ.filter (fun c => t.quotient (i.predAbove c) = a)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]

end ConsecutiveFusion
end FreeProbability

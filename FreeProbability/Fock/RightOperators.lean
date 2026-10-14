import FreeProbability.Fock.WickWord

/-! # Word reversal and right semicircular operators -/

noncomputable section
open scoped Classical InnerProductSpace ENNReal

namespace FreeProbability.Fock

variable {I : Type*}

private theorem orthonormal_reverse :
    Orthonormal ℂ (fun w : List I => word w.reverse) := by
  rw [orthonormal_iff_ite]
  intro u v
  rw [inner_word]
  simp

/-- Unitary word reversal, initially given as an isometry. -/
def reversalIsometry : WordSpace I →ₗᵢ[ℂ] WordSpace I :=
  orthonormal_reverse.orthogonalFamily.linearIsometry

/-- Bounded word reversal. -/
def reversal : WordSpace I →L[ℂ] WordSpace I :=
  reversalIsometry.toContinuousLinearMap

@[simp] theorem reversal_word (w : List I) : reversal (word w) = word w.reverse := by
  change orthonormal_reverse.orthogonalFamily.linearIsometry (lp.single 2 w 1) = _
  rw [OrthogonalFamily.linearIsometry_apply_single]
  simp [LinearIsometry.toSpanSingleton_apply]

@[simp] theorem reversal_vacuum : reversal (vacuum : WordSpace I) = vacuum := by
  simp [vacuum]

/-- Reversal is involutive on the completed Hilbert space. -/
theorem reversal_mul_reversal : (reversal : WordSpace I →L[ℂ] WordSpace I) * reversal = 1 := by
  apply sub_eq_zero.mp
  apply eq_zero_of_word
  intro w
  simp [mul_apply_eq_comp]

@[simp] theorem reversal_reversal (f : WordSpace I) : reversal (reversal f) = f := by
  have h := congrArg (fun T : WordSpace I →L[ℂ] WordSpace I => T f) reversal_mul_reversal
  simpa [mul_apply_eq_comp] using h

@[simp] theorem adjoint_reversal :
    (reversal : WordSpace I →L[ℂ] WordSpace I).adjoint = reversal := by
  have hr : (reversal : WordSpace I →L[ℂ] WordSpace I).adjoint * reversal = 1 :=
    reversalIsometry.adjoint_comp_self
  calc
    reversal.adjoint = reversal.adjoint * (reversal * reversal) := by
      rw [reversal_mul_reversal, mul_one]
    _ = (reversal.adjoint * reversal) * reversal := by rw [mul_assoc]
    _ = reversal := by rw [hr, one_mul]

/-- Right semicircular operator, conjugate to its left counterpart by reversal. -/
def rightSemicircular (i : I) : WordSpace I →L[ℂ] WordSpace I :=
  reversal * semicircular i * reversal

@[simp] theorem adjoint_rightSemicircular (i : I) :
    (rightSemicircular i).adjoint = rightSemicircular i := by
  change star (rightSemicircular i) = rightSemicircular i
  simp [rightSemicircular, star_mul, ContinuousLinearMap.star_eq_adjoint, mul_assoc]

@[simp] theorem rightSemicircular_vacuum (i : I) :
    rightSemicircular i (vacuum : WordSpace I) = word [i] := by
  simp [rightSemicircular, mul_apply_eq_comp]

/-- Right creation appends a letter; right annihilation deletes the last matching letter. -/
@[simp] theorem rightSemicircular_word_append (i j : I) (w : List I) :
    rightSemicircular i (word (w ++ [j])) =
      word (w ++ [j, i]) + if i = j then word w else 0 := by
  simp only [rightSemicircular, mul_apply_eq_comp, reversal_word, List.reverse_append,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
    semicircular, add_apply, creation_word, annihilation_word, map_add]
  by_cases h : i = j <;> simp [h, List.append_assoc]

@[simp] theorem rightSemicircular_word_nil (i : I) :
    rightSemicircular i (word ([] : List I)) = word [i] :=
  rightSemicircular_vacuum i

@[simp] theorem rightSemicircular_word_singleton (i j : I) :
    rightSemicircular i (word [j]) = word [j, i] + if i = j then word [] else 0 := by
  simpa using rightSemicircular_word_append i j []

@[simp] theorem rightSemicircular_word_cons_append (i k j : I) (w : List I) :
    rightSemicircular i (word (k :: (w ++ [j]))) =
      word (k :: (w ++ [j, i])) + if i = j then word (k :: w) else 0 := by
  exact rightSemicircular_word_append i j (k :: w)

@[simp] theorem rightSemicircular_word_pair (i k j : I) :
    rightSemicircular i (word [k, j]) =
      word [k, j, i] + if i = j then word [k] else 0 := by
  exact rightSemicircular_word_cons_append i k j []

@[simp] theorem rightSemicircular_word_cons_cons_append (i k m j : I) (w : List I) :
    rightSemicircular i (word (k :: m :: (w ++ [j]))) =
      word (k :: m :: (w ++ [j, i])) + if i = j then word (k :: m :: w) else 0 := by
  exact rightSemicircular_word_append i j (k :: m :: w)

/-- Left and right semicircular operators commute, including the vacuum boundary. -/
theorem commute_semicircular_rightSemicircular (i j : I) :
    Commute (semicircular i) (rightSemicircular j) := by
  apply sub_eq_zero.mp
  apply eq_zero_of_word
  intro w
  simp only [sub_apply, mul_apply_eq_comp]
  apply sub_eq_zero.mpr
  cases w with
  | nil =>
    change semicircular i (rightSemicircular j vacuum) =
      rightSemicircular j (semicircular i vacuum)
    rw [rightSemicircular_vacuum, semicircular_vacuum]
    have hr := rightSemicircular_word_append j i []
    simp only [List.nil_append] at hr
    rw [hr]
    simp only [semicircular, add_apply, creation_word, annihilation_word]
    by_cases h : i = j <;> simp [h, eq_comm]
  | cons k w =>
    cases w using List.reverseRecOn with
    | nil =>
      have hr := rightSemicircular_word_append j k []
      simp only [List.nil_append] at hr
      rw [hr]
      simp only [semicircular, add_apply, creation_word, annihilation_word, map_add]
      by_cases hik : i = k <;> by_cases hjk : j = k <;>
        simp [hik, hjk, add_comm]
    | append_singleton w l ih =>
      rw [show k :: (w ++ [l]) = (k :: w) ++ [l] from rfl,
        rightSemicircular_word_append]
      simp only [semicircular, add_apply, creation_word, annihilation_word, map_add]
      by_cases hik : i = k <;> by_cases hjl : j = l <;>
        simp [hik, hjl, creation_word, annihilation_word,
          add_comm, add_left_comm]

end FreeProbability.Fock

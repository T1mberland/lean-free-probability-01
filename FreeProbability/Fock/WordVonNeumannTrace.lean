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

/-- Right Wick polynomials with the actual unreversed word as vacuum vector. -/
def rightWick (w : List I) : WordSpace I →L[ℂ] WordSpace I :=
  reversal * wick w.reverse * reversal

theorem rightWick_vacuum (w : List I) : rightWick w (vacuum : WordSpace I) = word w := by
  simp only [rightWick, mul_apply_eq_comp, reversal_vacuum, wick_vacuum, reversal_word,
    List.reverse_reverse]

theorem star_rightWick_vacuum (w : List I) :
    star (rightWick w) (vacuum : WordSpace I) = word w.reverse := by
  have hr : star (reversal : WordSpace I →L[ℂ] WordSpace I) = reversal := adjoint_reversal
  simp only [rightWick, star_mul, hr, mul_apply_eq_comp, reversal_vacuum,
    star_wick_vacuum, List.reverse_reverse, reversal_word]

theorem commute_rightWick (T : WordSpace I →L[ℂ] WordSpace I)
    (hT : ∀ i, Commute T (rightSemicircular i)) (w : List I) : Commute T (rightWick w) := by
  have hs (i : I) : Commute (reversal * T * reversal) (semicircular i) := by
    apply ContinuousLinearMap.ext
    intro f
    have h := congrArg (fun U : WordSpace I →L[ℂ] WordSpace I => reversal (U (reversal f)))
      (hT i).eq
    simpa only [rightSemicircular, mul_apply_eq_comp, reversal_reversal] using h
  apply ContinuousLinearMap.ext
  intro f
  have h := congrArg (fun U : WordSpace I →L[ℂ] WordSpace I => reversal (U (reversal f)))
    (commute_wick (reversal * T * reversal) hs w.reverse).eq
  simpa only [rightWick, mul_apply_eq_comp, reversal_reversal] using h

theorem reversal_coefficient (f : WordSpace I) (w : List I) : reversal f w = f w.reverse := by
  rw [← inner_word_left, ← ContinuousLinearMap.adjoint_inner_left, adjoint_reversal,
    reversal_word, inner_word_left]

/-- Conjugate reversal is the genuine anti-linear vacuum involution. -/
def vacuumConjugateReversal (f : WordSpace I) : WordSpace I := star (reversal f)

theorem vacuumConjugateReversal_inner (f g : WordSpace I) :
    inner ℂ (vacuumConjugateReversal f) g = inner ℂ (vacuumConjugateReversal g) f := by
  let e : Equiv.Perm (List I) :=
    Function.Involutive.toPerm (List.reverse : List I → List I) List.reverse_reverse
  have he (w : List I) : e w = w.reverse := rfl
  have h := e.tsum_eq (fun w => f w * g w.reverse)
  simp only [he, List.reverse_reverse] at h
  simpa only [vacuumConjugateReversal, lp.inner_eq_tsum, lp.star_apply,
    reversal_coefficient, RCLike.inner_apply, starRingEnd_apply, star_star, mul_comm] using h

/-- Every operator commuting with the full right fields obeys the actual vacuum conjugation law. -/
theorem star_vacuum_eq_conjugateReversal (T : WordSpace I →L[ℂ] WordSpace I)
    (hT : ∀ i, Commute T (rightSemicircular i)) :
    star T (vacuum : WordSpace I) = vacuumConjugateReversal (T vacuum) := by
  apply lp.ext
  funext w
  have hc := congrArg (fun U : WordSpace I →L[ℂ] WordSpace I => U vacuum)
    (commute_rightWick T hT w).eq
  calc
    (star T (vacuum : WordSpace I)) w = inner ℂ (word w) (star T vacuum) :=
      (inner_word_left w _).symm
    _ = inner ℂ (T (word w)) vacuum := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
    _ = inner ℂ (T (rightWick w vacuum)) vacuum := by rw [rightWick_vacuum]
    _ = inner ℂ (rightWick w (T vacuum)) vacuum := congrArg (fun x => inner ℂ x vacuum) hc
    _ = inner ℂ (T vacuum) (star (rightWick w) vacuum) := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
    _ = inner ℂ (T vacuum) (word w.reverse) := by rw [star_rightWick_vacuum]
    _ = star ((T vacuum) w.reverse) := by rw [← inner_conj_symm, inner_word_left, starRingEnd_apply]
    _ = vacuumConjugateReversal (T vacuum) w := by
      rw [vacuumConjugateReversal, lp.star_apply, reversal_coefficient]

/-- Vacuum trace on the full right-field commutant, with no density premise. -/
theorem vacuumExpectation_mul_comm_of_commute_right
    (T U : WordSpace I →L[ℂ] WordSpace I)
    (hT : ∀ i, Commute T (rightSemicircular i))
    (hU : ∀ i, Commute U (rightSemicircular i)) :
    vacuumExpectation (T * U) = vacuumExpectation (U * T) := by
  change inner ℂ vacuum (T (U vacuum)) = inner ℂ vacuum (U (T vacuum))
  calc
    _ = inner ℂ (star T vacuum) (U vacuum) := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    _ = inner ℂ (vacuumConjugateReversal (T vacuum)) (U vacuum) := by
      rw [star_vacuum_eq_conjugateReversal T hT]
    _ = inner ℂ (vacuumConjugateReversal (U vacuum)) (T vacuum) :=
      vacuumConjugateReversal_inner _ _
    _ = inner ℂ (star U vacuum) (T vacuum) := by
      rw [star_vacuum_eq_conjugateReversal U hU]
    _ = _ := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]

/-- Genuine traciality of the vacuum on the literal generated von Neumann algebra. -/
theorem wordSemicircularVonNeumannAlgebra_vacuum_tracial
    {T U : WordSpace I →L[ℂ] WordSpace I}
    (hT : T ∈ wordSemicircularVonNeumannAlgebra I)
    (hU : U ∈ wordSemicircularVonNeumannAlgebra I) :
    vacuumExpectation (T * U) = vacuumExpectation (U * T) :=
  vacuumExpectation_mul_comm_of_commute_right T U
    (wordSemicircularVonNeumannAlgebra_commute_right hT)
    (wordSemicircularVonNeumannAlgebra_commute_right hU)

/-- Actual positive normalized vacuum state on the literal generated double commutant. -/
def wordVonNeumannVacuumState (I : Type*) : StarProbabilitySpace (wordSemicircularDoubleAlgebra I) where
  expectation := vacuumLinear.comp (wordSemicircularDoubleAlgebra I).val.toLinearMap
  map_one := vacuumExpectation_one
  map_star T := vacuumExpectation_star (T : WordSpace I →L[ℂ] WordSpace I)
  positive T := (vacuumState I).positive (T : WordSpace I →L[ℂ] WordSpace I)

theorem wordVonNeumannVacuumState_isFaithful (I : Type*) :
    IsFaithful (wordVonNeumannVacuumState I).toProbabilitySpace := by
  intro T hT
  apply Subtype.ext
  exact wordSemicircularVonNeumannAlgebra_vacuum_faithful T.property hT

theorem wordVonNeumannVacuumState_isTracial (I : Type*) :
    IsTracial (wordVonNeumannVacuumState I).toProbabilitySpace := by
  intro T U
  exact wordSemicircularVonNeumannAlgebra_vacuum_tracial T.property U.property

end FreeProbability.Fock

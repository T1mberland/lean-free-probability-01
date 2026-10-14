import FreeProbability.Fock.FreeCStarModel

/-! # The vacuum boundary commutator for right creation and annihilation -/

noncomputable section
open scoped Classical InnerProductSpace

namespace FreeProbability.Fock

variable {I : Type*}

/-- Projection onto the vacuum line in the actual completed Hilbert space. -/
def vacuumProjection : WordSpace I →L[ℂ] WordSpace I :=
  InnerProductSpace.rankOne ℂ vacuum vacuum

@[simp] theorem vacuumProjection_word (w : List I) :
    vacuumProjection (word w) = if w = [] then vacuum else 0 := by
  simp only [vacuumProjection, InnerProductSpace.rankOne_apply, vacuum, inner_word]
  by_cases hw : w = [] <;> simp [hw, eq_comm]

@[simp] theorem adjoint_vacuumProjection :
    (vacuumProjection : WordSpace I →L[ℂ] WordSpace I).adjoint = vacuumProjection := by
  simp [vacuumProjection]

/-- Right creation appends the canonical basis letter. -/
def rightCreation (i : I) : WordSpace I →L[ℂ] WordSpace I :=
  reversal * creation i * reversal

/-- Right annihilation is the Hilbert adjoint of right creation. -/
def rightAnnihilation (i : I) : WordSpace I →L[ℂ] WordSpace I :=
  (rightCreation i).adjoint

@[simp] theorem rightCreation_word (i : I) (w : List I) :
    rightCreation i (word w) = word (w ++ [i]) := by
  simp [rightCreation, mul_apply_eq_comp, List.reverse_cons]

@[simp] theorem rightCreation_vacuum (i : I) :
    rightCreation i (vacuum : WordSpace I) = word [i] := by simp [vacuum]

@[simp] theorem rightAnnihilation_vacuum (i : I) :
    rightAnnihilation i (vacuum : WordSpace I) = 0 := by
  change (star (reversal * creation i * reversal) : WordSpace I →L[ℂ] WordSpace I) (vacuum : WordSpace I) = 0
  rw [star_mul, star_mul]
  simp only [ContinuousLinearMap.star_eq_adjoint, adjoint_reversal, mul_apply_eq_comp,
    reversal_vacuum]
  change reversal ((annihilation i) vacuum) = 0
  simp

/-- The only failure of left semicircular/right creation commutation occurs at the vacuum. -/
theorem semicircular_rightCreation_commutator (i j : I) :
    semicircular i * rightCreation j - rightCreation j * semicircular i =
      if i = j then vacuumProjection else 0 := by
  apply sub_eq_zero.mp
  apply eq_zero_of_word
  intro w
  simp only [sub_apply, mul_apply_eq_comp, rightCreation_word]
  cases w with
  | nil =>
    simp only [semicircular, add_apply, creation_word, annihilation_word,
      rightCreation_word, map_add]
    by_cases h : i = j <;> simp [h, vacuum]
  | cons k w =>
    simp only [semicircular, add_apply, creation_word, annihilation_word,
      rightCreation_word, map_add]
    by_cases hik : i = k <;> by_cases hij : i = j <;>
      simp_all [List.cons_append, vacuumProjection_word]

/-- Right annihilation differentiates left semicircular words through a vacuum rank-one term. -/
theorem rightAnnihilation_semicircular_commutator (i j : I) :
    rightAnnihilation i * semicircular j - semicircular j * rightAnnihilation i =
      if i = j then vacuumProjection else 0 := by
  have h := congrArg (star : (WordSpace I →L[ℂ] WordSpace I) → (WordSpace I →L[ℂ] WordSpace I))
    (semicircular_rightCreation_commutator j i)
  change ContinuousLinearMap.adjoint ((semicircular j).comp (rightCreation i) -
      (rightCreation i).comp (semicircular j)) = ContinuousLinearMap.adjoint
      (if j = i then vacuumProjection else 0) at h
  simp only [map_sub, ContinuousLinearMap.adjoint_comp, adjoint_semicircular] at h
  by_cases hij : i = j <;>
    simpa [hij, eq_comm, ContinuousLinearMap.star_eq_adjoint, rightAnnihilation, ContinuousLinearMap.mul_def] using h

/-- Rank-one vacuum insertions factor the two surrounding expectations. -/
theorem vacuumExpectation_mul_vacuumProjection_mul
    (T U : WordSpace I →L[ℂ] WordSpace I) :
    vacuumExpectation (T * vacuumProjection * U) = vacuumExpectation T * vacuumExpectation U := by
  simp [vacuumExpectation, vacuumProjection, InnerProductSpace.rankOne_apply,
    mul_apply_eq_comp, inner_smul_right, mul_comm]

end FreeProbability.Fock

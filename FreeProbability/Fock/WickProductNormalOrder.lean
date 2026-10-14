import FreeProbability.Fock.WickWord

/-! # Actual normal-order expansion of the bounded Wick operators -/

noncomputable section
open scoped Classical

namespace FreeProbability.Fock

variable {I : Type*}

/-- Ordered product of the actual left creation operators. -/
def creationWord (w : List I) : WordSpace I →L[ℂ] WordSpace I := (w.map creation).prod

/-- Ordered product of the actual annihilation operators. -/
def annihilationWord (w : List I) : WordSpace I →L[ℂ] WordSpace I := (w.map annihilation).prod

@[simp] theorem creationWord_nil : creationWord ([] : List I) = 1 := rfl
@[simp] theorem annihilationWord_nil : annihilationWord ([] : List I) = 1 := rfl
@[simp] theorem creationWord_cons (i : I) (w : List I) :
    creationWord (i :: w) = creation i * creationWord w := rfl
@[simp] theorem annihilationWord_cons (i : I) (w : List I) :
    annihilationWord (i :: w) = annihilation i * annihilationWord w := rfl

/-- The actual normal-ordered expansion contains exactly one term for each cut. -/
def wickNormalOrder (w : List I) : WordSpace I →L[ℂ] WordSpace I :=
  ∑ k : Fin (w.length + 1), creationWord (w.take k.val) * annihilationWord (w.drop k.val)

@[simp] theorem wickNormalOrder_nil : wickNormalOrder ([] : List I) = 1 := by
  simp [wickNormalOrder]

/-- Splitting off the zero cut gives the exact creation-annihilation recurrence. -/
theorem wickNormalOrder_cons (i : I) (w : List I) :
    wickNormalOrder (i :: w) =
      creation i * wickNormalOrder w + annihilation i * annihilationWord w := by
  unfold wickNormalOrder
  simp only [List.length_cons]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, List.take_zero, creationWord_nil, one_mul,
    List.drop_zero, annihilationWord_cons, List.take_succ_cons, creationWord_cons,
    List.drop_succ_cons]
  rw [Finset.mul_sum]
  simp only [mul_assoc]
  abel

/-- The annihilator contracts precisely the first creation, leaving the fully annihilating term. -/
theorem annihilation_wickNormalOrder_cons (i j : I) (w : List I) :
    annihilation i * wickNormalOrder (j :: w) =
      (if i = j then wickNormalOrder w else 0) +
        annihilation i * annihilationWord (j :: w) := by
  have hac : annihilation i * creation j =
      if i = j then (1 : WordSpace I →L[ℂ] WordSpace I) else 0 := annihilation_creation i j
  rw [wickNormalOrder_cons, mul_add, ← mul_assoc, hac]
  by_cases h : i = j <;> simp [h, annihilationWord_cons]

/-- The recursively defined Wick polynomial is exactly the normal-ordered bounded operator sum. -/
theorem wick_eq_normalOrder (w : List I) : wick w = wickNormalOrder w := by
  induction w using List.twoStepInduction with
  | nil => simp
  | singleton i => simp [wickNormalOrder_cons, semicircular]
  | cons_cons i j w h₁ h₂ =>
    change semicircular i * wick (j :: w) - (if i = j then wick w else 0) = _
    rw [h₂ j, h₁, semicircular, add_mul, annihilation_wickNormalOrder_cons,
      wickNormalOrder_cons i (j :: w)]
    abel

/-- Literal normal-order formula, one creation-prefix/annihilation-suffix term at each cut. -/
theorem wick_normal_order_expansion (w : List I) :
    wick w = ∑ k : Fin (w.length + 1),
      creationWord (w.take k.val) * annihilationWord (w.drop k.val) :=
  wick_eq_normalOrder w

end FreeProbability.Fock

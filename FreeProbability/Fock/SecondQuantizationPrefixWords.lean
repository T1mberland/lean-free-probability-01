import FreeProbability.Fock.LengthDecomposition

/-! # Ordered prefix/tail decomposition of doubled-alphabet words

The tail is empty or starts with a letter outside the included alphabet.
No commutation, reordering, spanning, or countability assumption is involved.
-/
noncomputable section
namespace FreeProbability.Fock

/-- A tail is empty or begins with an outside letter and continues with an arbitrary word. -/
abbrev PrefixTail (I J : Type*) := Option (J × List (Sum I J))

def prefixTailWord {I J : Type*} : PrefixTail I J → List (Sum I J)
  | none => []
  | some (j, w) => Sum.inr j :: w

/-- Exact ordered concatenation of the included prefix and the outside-starting tail. -/
def joinPrefixTail {I J : Type*} (p : List I × PrefixTail I J) : List (Sum I J) :=
  p.1.map Sum.inl ++ prefixTailWord p.2

/-- Split at the first outside letter, retaining the order of every letter. -/
def splitPrefixTail {I J : Type*} : List (Sum I J) → List I × PrefixTail I J
  | [] => ([], none)
  | Sum.inl i :: w => (i :: (splitPrefixTail w).1, (splitPrefixTail w).2)
  | Sum.inr j :: w => ([], some (j, w))

@[simp] theorem join_splitPrefixTail {I J : Type*} (w : List (Sum I J)) :
    joinPrefixTail (splitPrefixTail w) = w := by
  induction w with
  | nil => rfl
  | cons a w hw =>
    cases a with
    | inl i => simpa [splitPrefixTail, joinPrefixTail] using congrArg (List.cons (Sum.inl i)) hw
    | inr j => rfl

@[simp] theorem split_joinPrefixTail {I J : Type*} (p : List I × PrefixTail I J) :
    splitPrefixTail (joinPrefixTail p) = p := by
  obtain ⟨w, t⟩ := p
  induction w with
  | nil => cases t with
    | none => rfl
    | some t => obtain ⟨j, v⟩ := t; rfl
  | cons i w hw =>
    change (i :: (splitPrefixTail (joinPrefixTail (w, t))).1,
      (splitPrefixTail (joinPrefixTail (w, t))).2) = _
    rw [hw]

/-- Every word has a unique included prefix and an empty or outside-starting tail. -/
def prefixTailEquiv (I J : Type*) : List (Sum I J) ≃ List I × PrefixTail I J where
  toFun := splitPrefixTail
  invFun := joinPrefixTail
  left_inv := join_splitPrefixTail
  right_inv := split_joinPrefixTail

@[simp] theorem prefixTailEquiv_cons_inl {I J : Type*} (i : I) (w : List (Sum I J)) :
    prefixTailEquiv I J (Sum.inl i :: w) =
      (i :: (prefixTailEquiv I J w).1, (prefixTailEquiv I J w).2) := rfl

end FreeProbability.Fock

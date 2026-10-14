import FreeProbability.Fock.WickProductWordAction
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fin.Rev

/-! # Exact tuple splitting and reversal for the normal-order coefficient matrices -/

noncomputable section
open scoped Classical

namespace FreeProbability.Fock

variable {I : Type*}

/-- Reverse all colors of a fixed-degree tuple. -/
def reverseWordTuple {n : ℕ} (a : Fin n → I) : Fin n → I := fun i => a i.rev

/-- Tuple reversal agrees with actual list reversal. -/
theorem ofFn_reverseWordTuple {n : ℕ} (a : Fin n → I) :
    List.ofFn (reverseWordTuple a) = (List.ofFn a).reverse := by
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    simp only [List.getElem_ofFn, List.getElem_reverse, List.length_ofFn]
    change a (Fin.rev ⟨j, _⟩) = a ⟨n - 1 - j, _⟩
    congr 1
    apply Fin.ext
    simp [Fin.rev]
    omega

/-- Split the original tuple into its prefix and its reversed suffix. -/
def wickTupleSplit (p q : ℕ) (a : Fin (p + q) → I) :
    (Fin p → I) × (Fin q → I) :=
  (fun i => a (i.castAdd q), fun j => a (j.rev.natAdd p))

/-- A normal-order prefix and reversed suffix determine all original colors uniquely. -/
theorem wickTupleSplit_injective (p q : ℕ) : Function.Injective (wickTupleSplit (I := I) p q) := by
  intro a b h
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · exact congrFun (congrArg Prod.fst h) j
  · have he := congrFun (congrArg Prod.snd h) j.rev
    simpa only [wickTupleSplit, Fin.rev_rev] using he

/-- The actual word splits into its prefix and the reverse of its reversed suffix tuple. -/
theorem ofFn_wickTupleSplit (p q : ℕ) (a : Fin (p + q) → I) :
    List.ofFn a = List.ofFn (wickTupleSplit p q a).1 ++
      (List.ofFn (wickTupleSplit p q a).2).reverse := by
  have h := List.ofFn_add (f := a)
  have he : (wickTupleSplit p q a).2 = reverseWordTuple (fun j : Fin q => a (j.natAdd p)) := rfl
  rw [he, ofFn_reverseWordTuple, List.reverse_reverse]
  convert h using 1
  apply congrArg₂ List.append _ rfl
  apply congrArg List.ofFn
  funext i
  apply congrArg a
  exact Fin.ext rfl

/-- The prefix coefficient coordinate agrees with the exact normal-order cut. -/
theorem ofFn_wickTupleSplit_fst (p q : ℕ) (a : Fin (p + q) → I) :
    List.ofFn (wickTupleSplit p q a).1 = (List.ofFn a).take p := by
  rw [ofFn_wickTupleSplit p q a]
  have h : (List.ofFn (wickTupleSplit p q a).1 ++
      (List.ofFn (wickTupleSplit p q a).2).reverse).take
      (List.ofFn (wickTupleSplit p q a).1).length = List.ofFn (wickTupleSplit p q a).1 :=
    List.take_left
  simpa only [List.length_ofFn] using h.symm

/-- The reversed suffix coefficient coordinate agrees with the exact normal-order cut. -/
theorem ofFn_wickTupleSplit_snd_reverse (p q : ℕ) (a : Fin (p + q) → I) :
    (List.ofFn (wickTupleSplit p q a).2).reverse = (List.ofFn a).drop p := by
  rw [ofFn_wickTupleSplit p q a]
  have h : (List.ofFn (wickTupleSplit p q a).1 ++
      (List.ofFn (wickTupleSplit p q a).2).reverse).drop
      (List.ofFn (wickTupleSplit p q a).1).length = (List.ofFn (wickTupleSplit p q a).2).reverse :=
    List.drop_left
  simpa only [List.length_ofFn] using h.symm

end FreeProbability.Fock

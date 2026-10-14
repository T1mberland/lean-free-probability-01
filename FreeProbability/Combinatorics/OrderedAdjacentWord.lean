import FreeProbability.Combinatorics.BlockWordTransport
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Lean.Elab.Tactic.Omega

/-!
# Adjacent positions and ordered word multiplication

Two consecutive positions retained in a block remain consecutive in its ordered
enumeration. Multiplying consecutive entries reduces a word by one entry while
preserving its noncommutative ordered product.
-/

namespace FreeProbability

variable {n : ℕ}

/-- Globally adjacent retained positions are adjacent in the ordered block enumeration. -/
theorem block_indices_adjacent (s : Finset (Fin n)) (a b : Fin n)
    (ha : a ∈ s) (hb : b ∈ s) (hab : a.val + 1 = b.val) :
    ((s.orderIsoOfFin rfl).symm ⟨a, ha⟩).val + 1 =
      ((s.orderIsoOfFin rfl).symm ⟨b, hb⟩).val := by
  let u := (s.orderIsoOfFin rfl).symm ⟨a, ha⟩
  let v := (s.orderIsoOfFin rfl).symm ⟨b, hb⟩
  have hab' : a < b := by change a.val < b.val; omega
  have huv : u < v := (s.orderIsoOfFin rfl).symm.lt_iff_lt.mpr hab'
  change u.val + 1 = v.val
  by_contra h
  have hgap : u.val + 1 < v.val := by have hv : u.val < v.val := huv; omega
  let k : Fin s.card := ⟨u.val + 1, lt_trans hgap v.isLt⟩
  have huk : u < k := by change u.val < u.val + 1; omega
  have hkv : k < v := hgap
  have hfu : s.orderEmbOfFin rfl u = a :=
    congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨a, ha⟩)
  have hfv : s.orderEmbOfFin rfl v = b :=
    congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨b, hb⟩)
  have hak := (s.orderEmbOfFin rfl).lt_iff_lt.mpr huk
  have hkb := (s.orderEmbOfFin rfl).lt_iff_lt.mpr hkv
  rw [hfu] at hak
  rw [hfv] at hkb
  have hakv : a.val < (s.orderEmbOfFin rfl k).val := hak
  have hkbv : (s.orderEmbOfFin rfl k).val < b.val := hkb
  omega

variable {A : Type*} [Monoid A]

/-- Fuse two adjacent entries, retaining the increasing order of every other entry. -/
def fuseAdjacent (x : Fin (n + 1) → A) (i : Fin n) : Fin n → A :=
  Function.update (x ∘ i.castSucc.succAbove) i (x i.castSucc * x i.succ)

@[simp] theorem fuseAdjacent_at (x : Fin (n + 1) → A) (i : Fin n) :
    fuseAdjacent x i i = x i.castSucc * x i.succ := by
  classical
  simp [fuseAdjacent]

@[simp] theorem fuseAdjacent_zero (x : Fin (n + 2) → A) :
    fuseAdjacent x (0 : Fin (n + 1)) =
      Fin.cons (x 0 * x 1) (fun j : Fin n => x j.succ.succ) := by
  classical
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [fuseAdjacent]
  · simp [fuseAdjacent]

@[simp] theorem fuseAdjacent_succ (x : Fin (n + 2) → A) (i : Fin n) :
    fuseAdjacent x i.succ = Fin.cons (x 0) (fuseAdjacent (fun j => x j.succ) i) := by
  classical
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [fuseAdjacent, Function.update_of_ne (Ne.symm (Fin.succ_ne_zero i)),
      Function.comp_apply, Fin.castSucc_succ, Fin.succ_succAbove_zero, Fin.cons_zero]
  · by_cases hji : j = i
    · subst j
      simp [fuseAdjacent]
    · simp [fuseAdjacent, hji, Fin.succ_succAbove_succ]

/-- Adjacent fusion preserves the exact ordered product in any monoid. -/
theorem prod_ofFn_fuseAdjacent (x : Fin (n + 1) → A) (i : Fin n) :
    (List.ofFn (fuseAdjacent x i)).prod = (List.ofFn x).prod := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [fuseAdjacent_zero]
      simp [List.ofFn_succ, mul_assoc]
    · rw [fuseAdjacent_succ]
      simp only [List.ofFn_cons, List.prod_cons]
      rw [ih]
      simp only [List.ofFn_succ, List.prod_cons]

end FreeProbability

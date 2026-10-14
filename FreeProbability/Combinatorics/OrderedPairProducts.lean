import FreeProbability.Combinatorics.ConsecutiveFusionWord
import FreeProbability.Combinatorics.NoncrossingInterleave

/-! # Exact ordered products of alternating pairs -/

namespace FreeProbability

open NoncrossingPartition

variable {n : ℕ}

theorem halfPosition_monotone : Monotone (halfPosition : Fin (2 * n) → Fin n) := by
  intro a b hab
  change a.val / 2 ≤ b.val / 2
  exact Nat.div_le_div_right hab

theorem halfPosition_surjective : Function.Surjective (halfPosition : Fin (2 * n) → Fin n) :=
  fun a => ⟨oddPosition a, halfPosition_odd a⟩

/-- The half-position quotient has precisely the adjacent original/complementary pair as each fiber. -/
theorem halfPosition_fiber (a : Fin n) :
    Finset.univ.filter (fun b : Fin (2 * n) => halfPosition b = a) =
      {oddPosition a, evenPosition a} := by
  classical
  ext b
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    rcases position_cases b with hb | hb
    · left
      simpa only [h] using hb
    · right
      simpa only [h] using hb
  · rintro (rfl | rfl)
    · exact halfPosition_odd a
    · exact halfPosition_even a

/-- Each two-position interval product is exactly its ordered pair product. -/
theorem intervalProducts_halfPosition {A : Type*} [Monoid A] (x : Fin (2 * n) → A) :
    intervalProducts halfPosition x = fun a => x (oddPosition a) * x (evenPosition a) := by
  classical
  funext a
  unfold intervalProducts
  rw [halfPosition_fiber]
  have hle : oddPosition a ≤ evenPosition a := by
    change 2 * a.val ≤ 2 * a.val + 1
    omega
  have hne : oddPosition a ≠ evenPosition a := by
    intro h
    have hv := congrArg Fin.val h
    change 2 * a.val = 2 * a.val + 1 at hv
    omega
  unfold orderedBlockWord
  rw [Finset.sort_insert (· ≤ ·) (by intro b hb; simpa only [Finset.mem_singleton.mp hb] using hle)
    (by simpa only [Finset.mem_singleton] using hne)]
  simp only [Finset.sort_singleton, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]

/-- Pair grouping preserves the ordered product without commuting entries. -/
theorem prod_ofFn_pairs {A : Type*} [Monoid A] (x : Fin (2 * n) → A) :
    (List.ofFn x).prod =
      (List.ofFn (fun a => x (oddPosition a) * x (evenPosition a))).prod := by
  obtain ⟨t, ht⟩ := ConsecutiveFusion.exists_quotient_eq halfPosition
    halfPosition_monotone halfPosition_surjective
  have hw := t.applyWord_eq_intervalProducts x
  rw [ht, intervalProducts_halfPosition] at hw
  rw [← hw]
  exact (t.prod_applyWord x).symm

/-- Alternate the entries of two tuples, beginning with the first tuple. -/
def interleavedWord {A : Type*} (a b : Fin n → A) (i : Fin (2 * n)) : A :=
  if i.val % 2 = 0 then a (halfPosition i) else b (halfPosition i)

@[simp] theorem interleavedWord_odd {A : Type*} (a b : Fin n → A) (i : Fin n) :
    interleavedWord a b (oddPosition i) = a i := by
  simp [interleavedWord, oddPosition, halfPosition]

@[simp] theorem interleavedWord_even {A : Type*} (a b : Fin n → A) (i : Fin n) :
    interleavedWord a b (evenPosition i) = b i := by
  change (if (2 * i.val + 1) % 2 = 0 then a (halfPosition (evenPosition i))
    else b (halfPosition (evenPosition i))) = b i
  rw [halfPosition_even]
  have hne : (2 * i.val + 1) % 2 ≠ 0 := by omega
  simp only [hne, ite_false]

end FreeProbability

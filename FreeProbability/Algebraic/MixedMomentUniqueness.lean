import FreeProbability.Algebraic.Freeness
import Mathlib.Tactic.Push

/-!
# Free mixed moments are determined by the marginals

The induction shortens a word by multiplying adjacent letters from the same
subalgebra. For an alternating word, centering preserves the difference of the
two expectations once all shorter words agree. Freeness then makes that difference
zero. No positivity, trace, or analytic hypothesis is required.
-/

namespace FreeProbability

variable {𝕜 A I : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]

/-- Ordered product of the algebra entries of a labeled word. -/
def wordProduct (w : List (I × A)) : A := (w.map Prod.snd).prod

@[simp] theorem wordProduct_nil : wordProduct ([] : List (I × A)) = (1 : A) := rfl

@[simp] theorem wordProduct_cons (x : I × A) (w : List (I × A)) :
    wordProduct (x :: w) = x.2 * wordProduct w := rfl

@[simp] theorem wordProduct_append (u v : List (I × A)) :
    wordProduct (u ++ v) = wordProduct u * wordProduct v := by
  simp [wordProduct, List.prod_append]

/-- Center all letters without changing their subalgebra labels. -/
def centerWord (φ : ProbabilitySpace 𝕜 A) (w : List (I × A)) : List (I × A) :=
  w.map (fun x => (x.1, φ.center x.2))

@[simp] theorem centerWord_length (φ : ProbabilitySpace 𝕜 A) (w : List (I × A)) :
    (centerWord φ w).length = w.length := List.length_map _

theorem linearMap_center_insert (E : A →ₗ[𝕜] 𝕜) (φ : ProbabilitySpace 𝕜 A)
    (u v : List (I × A)) (x : I × A) :
    E (wordProduct (u ++ (x.1, φ.center x.2) :: v)) =
      E (wordProduct (u ++ x :: v)) - φ.expectation x.2 * E (wordProduct (u ++ v)) := by
  simp only [wordProduct_append, wordProduct_cons, ProbabilitySpace.center,
    sub_mul, mul_sub, Algebra.algebraMap_eq_smul_one,
    Algebra.smul_mul_assoc, Algebra.mul_smul_comm, one_mul, map_sub,
    map_smul, smul_eq_mul]

/-- Centering does not change a linear functional on a word if it annihilates all
shorter words in the same family of subalgebras. -/
theorem centerWord_preserves_of_shorter_zero (E : A →ₗ[𝕜] 𝕜)
    (φ : ProbabilitySpace 𝕜 A) (B : I → Subalgebra 𝕜 A)
    (u v : List (I × A))
    (hmem : ∀ x ∈ u ++ v, x.2 ∈ B x.1)
    (hshort : ∀ w : List (I × A), w.length < (u ++ v).length →
      (∀ x ∈ w, x.2 ∈ B x.1) → E (wordProduct w) = 0) :
    E (wordProduct (u ++ centerWord φ v)) = E (wordProduct (u ++ v)) := by
  induction v generalizing u with
  | nil => simp [centerWord]
  | cons x v ih =>
    have hx : x.2 ∈ B x.1 := hmem x (by simp)
    have hm : ∀ y ∈ (u ++ [(x.1, φ.center x.2)]) ++ v, y.2 ∈ B y.1 := by
      intro y hy
      simp only [List.mem_append, List.mem_singleton] at hy
      rcases hy with (hy | rfl) | hy
      · exact hmem y (by simp [hy])
      · exact φ.center_mem _ hx
      · exact hmem y (by simp [hy])
    have hs : ∀ w : List (I × A), w.length < ((u ++ [(x.1, φ.center x.2)]) ++ v).length →
        (∀ y ∈ w, y.2 ∈ B y.1) → E (wordProduct w) = 0 := by
      intro w hw hwmem
      apply hshort w _ hwmem
      simp only [List.length_append, List.length_cons, List.length_nil] at hw ⊢
      omega
    have hz : E (wordProduct (u ++ v)) = 0 := by
      apply hshort (u ++ v)
      · simp
      · intro y hy
        exact hmem y (by simpa only [List.mem_append, List.mem_cons] using
          (List.mem_append.mp hy).imp id Or.inr)
    calc
      E (wordProduct (u ++ centerWord φ (x :: v))) =
          E (wordProduct ((u ++ [(x.1, φ.center x.2)]) ++ centerWord φ v)) := by
            simp [centerWord, List.append_assoc]
      _ = E (wordProduct ((u ++ [(x.1, φ.center x.2)]) ++ v)) := ih _ hm hs
      _ = E (wordProduct (u ++ x :: v)) := by
        simp only [List.append_assoc, List.singleton_append]
        rw [linearMap_center_insert, hz, mul_zero, sub_zero]

namespace FreelyIndependent

/-- All mixed moments agree when the normalized expectations are free for the
same family and agree on each marginal subalgebra. -/
theorem mixed_moments_unique {φ ψ : ProbabilitySpace 𝕜 A}
    {B : I → Subalgebra 𝕜 A} (hφ : FreelyIndependent φ B)
    (hψ : FreelyIndependent ψ B)
    (hmarg : ∀ i (a : A), a ∈ B i → φ.expectation a = ψ.expectation a)
    (w : List (I × A)) (hmem : ∀ x ∈ w, x.2 ∈ B x.1) :
    φ.expectation (wordProduct w) = ψ.expectation (wordProduct w) := by
  classical
  suffices ∀ n (w : List (I × A)), w.length = n →
      (∀ x ∈ w, x.2 ∈ B x.1) →
      φ.expectation (wordProduct w) = ψ.expectation (wordProduct w) from
    this w.length w rfl hmem
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro w hw hmem
    by_cases hnil : w = []
    · simp [hnil]
    by_cases halt : w.IsChain (fun x y => x.1 ≠ y.1)
    · let E := φ.expectation - ψ.expectation
      have hs : ∀ v : List (I × A), v.length < ([] ++ w).length →
          (∀ x ∈ v, x.2 ∈ B x.1) → E (wordProduct v) = 0 := by
        intro v hv hm
        have he := ih v.length (by simpa [hw] using hv) v rfl hm
        exact sub_eq_zero.mpr he
      have hc := centerWord_preserves_of_shorter_zero E φ B [] w (by simpa using hmem) hs
      have halt' : (centerWord φ w).IsChain (fun x y => x.1 ≠ y.1) :=
        (List.isChain_map _).mpr halt
      have hm : ∀ x ∈ centerWord φ w, x.2 ∈ B x.1 := by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        exact φ.center_mem _ (hmem y hy)
      have hzφ : ∀ x ∈ centerWord φ w, φ.expectation x.2 = 0 := by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        exact φ.expectation_center _
      have hzψ : ∀ x ∈ centerWord φ w, ψ.expectation x.2 = 0 := by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        simp only [ProbabilitySpace.center, map_sub, ProbabilitySpace.expectation_algebraMap]
        rw [hmarg y.1 y.2 (hmem y hy), sub_self]
      have hcne : centerWord φ w ≠ [] := by simpa [centerWord] using hnil
      have hpφ := hφ _ hcne halt' hm hzφ
      have hpψ := hψ _ hcne halt' hm hzψ
      apply sub_eq_zero.mp
      change E (wordProduct w) = 0
      rw [← List.nil_append w, ← hc]
      change φ.expectation (wordProduct (centerWord φ w)) -
        ψ.expectation (wordProduct (centerWord φ w)) = 0
      simp only [wordProduct, hpφ, hpψ, sub_self]
    · rw [List.isChain_iff_forall_rel_of_append_cons_cons] at halt
      push Not at halt
      obtain ⟨x, y, u, v, hsplit, hxy⟩ := halt
      have hlabels : x.1 = y.1 := by simpa using hxy
      let z : I × A := (x.1, x.2 * y.2)
      have hx : x.2 ∈ B x.1 := hmem x (by simp [hsplit])
      have hy : y.2 ∈ B x.1 := by simpa [hlabels] using hmem y (by simp [hsplit])
      have hm : ∀ a ∈ u ++ z :: v, a.2 ∈ B a.1 := by
        intro a ha
        simp only [List.mem_append, List.mem_cons] at ha
        rcases ha with ha | rfl | ha
        · exact hmem a (by simp [hsplit, ha])
        · exact (B x.1).mul_mem hx hy
        · exact hmem a (by simp [hsplit, ha])
      have hlen : (u ++ z :: v).length < n := by
        simp only [hsplit, List.length_append, List.length_cons] at hw
        simp only [List.length_append, List.length_cons]
        omega
      have he := ih _ hlen _ rfl hm
      simpa [hsplit, z, mul_assoc] using he

end FreelyIndependent
end FreeProbability

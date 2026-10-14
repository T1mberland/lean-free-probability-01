import FreeProbability.Algebraic.CumulantUnit

/-!
# Simultaneous centering of higher cumulants

Scalar-shift invariance in one coordinate extends to all coordinates at once.
This lets higher mixed cumulants be evaluated on centered variables without
changing their value or their subalgebra membership.
-/

namespace FreeProbability

variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]

/-- Centering all coordinates preserves every free cumulant of order at least two. -/
theorem cumulant_ofFn_center (φ : ProbabilitySpace 𝕜 A) {n : ℕ} (hn : 2 ≤ n)
    (x : Fin n → A) :
    cumulant φ (List.ofFn (fun i => φ.center (x i))) = cumulant φ (List.ofFn x) := by
  classical
  let centeredOn (s : Finset (Fin n)) (i : Fin n) := if i ∈ s then φ.center (x i) else x i
  have h (s : Finset (Fin n)) : cumulant φ (List.ofFn (centeredOn s)) =
      cumulant φ (List.ofFn x) := by
    induction s using Finset.induction_on with
    | empty => simp only [centeredOn, Finset.notMem_empty, ite_false]
    | @insert i s hi ih =>
      have hp : centeredOn (insert i s) = Function.update (centeredOn s) i (φ.center (centeredOn s i)) := by
        funext j
        by_cases hji : j = i
        · subst j
          simp [centeredOn, hi]
        · simp [centeredOn, hji]
      rw [hp, cumulant_update_center φ hn]
      exact ih
  simpa only [centeredOn, Finset.mem_univ, ite_true] using h Finset.univ

/-- List form of simultaneous centering. -/
theorem cumulant_map_center (φ : ProbabilitySpace 𝕜 A) (w : List A) (hn : 2 ≤ w.length) :
    cumulant φ (w.map φ.center) = cumulant φ w := by
  have h := cumulant_ofFn_center φ hn w.get
  rw [← Function.comp_def, ← List.map_ofFn, List.ofFn_get] at h
  exact h

end FreeProbability

import FreeProbability.Algebraic.CumulantCharacterization

/-!
# Additivity of free cumulants

For a finite free family, coordinatewise sums have cumulants equal to the sum of
the corresponding marginal cumulants. Multilinear expansion ranges over all
label assignments; every nonconstant assignment vanishes by freeness. This is
the algebraic coefficient identity underlying additive R-transform convolution.
-/

namespace FreeProbability

variable {𝕜 A I : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A] [Fintype I]

/-- Cumulants add across a finite free family, even for different entries at each coordinate. -/
theorem FreelyIndependent.cumulant_ofFn_sum {φ : ProbabilitySpace 𝕜 A}
    {B : I → Subalgebra 𝕜 A} (hfree : FreelyIndependent φ B) {n : ℕ}
    (a : I → Fin n → A) (ha : ∀ i k, a i k ∈ B i) :
    cumulant φ (List.ofFn (fun k => ∑ i, a i k)) =
      ∑ i, cumulant φ (List.ofFn (a i)) := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [cumulant]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  let z : Fin n := ⟨0, hnpos⟩
  have hexpand : cumulant φ (List.ofFn (fun k => ∑ i, a i k)) =
      ∑ f : Fin n → I, cumulant φ (List.ofFn (fun k => a (f k) k)) := by
    simp only [cumulant_ofFn]
    exact (cumulantMultilinear φ n).map_sum (fun k i => a i k)
  rw [hexpand]
  symm
  apply Fintype.sum_of_injective (fun i : I => fun _ : Fin n => i)
  · intro i j h
    exact congrFun h z
  · intro f hf
    apply hfree.cumulant_ofFn_eq_zero_of_mixed (fun k => a (f k) k) f (fun k => ha (f k) k)
    by_contra hm
    apply hf
    refine ⟨f z, ?_⟩
    funext k
    by_contra he
    exact hm ⟨z, k, he⟩
  · intro i
    rfl

/-- Univariate cumulants of a finite sum of free variables are the sums of the marginal cumulants. -/
theorem FreelyIndependent.cumulant_replicate_sum {φ : ProbabilitySpace 𝕜 A}
    {B : I → Subalgebra 𝕜 A} (hfree : FreelyIndependent φ B) (a : I → A)
    (ha : ∀ i, a i ∈ B i) (n : ℕ) :
    cumulant φ (List.replicate n (∑ i, a i)) =
      ∑ i, cumulant φ (List.replicate n (a i)) := by
  simpa only [List.ofFn_const] using hfree.cumulant_ofFn_sum
    (fun i (_ : Fin n) => a i) (fun i _ => ha i)

end FreeProbability

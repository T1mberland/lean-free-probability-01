import FreeProbability.Fock.WickProductWordAction

/-! # Actual word creators, their adjoints, and equal-degree orthogonal ranges -/

noncomputable section
open scoped Classical InnerProductSpace

namespace FreeProbability.Fock

variable {I : Type*}

/-- Every ordered word creator is an isometry on the entire complete Fock space. -/
theorem norm_creationWord_apply (w : List I) (f : WordSpace I) : ‖creationWord w f‖ = ‖f‖ := by
  induction w with
  | nil => simp
  | cons i w ih => rw [creationWord_cons, mul_apply_eq_comp, norm_creation_apply, ih]

/-- The actual word creation isometry, with no finite-support restriction on its argument. -/
def creationWordIsometry (w : List I) : WordSpace I →ₗᵢ[ℂ] WordSpace I where
  toLinearMap := (creationWord w).toLinearMap
  norm_map' := norm_creationWord_apply w

/-- The actual Hilbert adjoint reverses the entire creator word into annihilators. -/
theorem star_creationWord (w : List I) : star (creationWord w) = annihilationWord w.reverse := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [creationWord_cons, star_mul, ih, List.reverse_cons, annihilationWord_append]
    rfl

/-- Equal-degree word creators have exactly the canonical Kronecker Gram relation. -/
theorem annihilationWord_reverse_creationWord (u v : List I) (hlen : u.length = v.length) :
    annihilationWord u.reverse * creationWord v =
      if u = v then (1 : WordSpace I →L[ℂ] WordSpace I) else 0 := by
  induction u generalizing v with
  | nil =>
    have hv : v = [] := List.length_eq_zero_iff.mp hlen.symm
    subst v
    simp
  | cons i u ih =>
    cases v with
    | nil => simp at hlen
    | cons j v =>
      have ht : u.length = v.length := by simpa using hlen
      have hac : annihilation i * creation j =
          if i = j then (1 : WordSpace I →L[ℂ] WordSpace I) else 0 := annihilation_creation i j
      rw [List.reverse_cons, annihilationWord_append, creationWord_cons]
      change (annihilationWord u.reverse * annihilation i) * (creation j * creationWord v) = _
      rw [show (annihilationWord u.reverse * annihilation i) * (creation j * creationWord v) =
        annihilationWord u.reverse * (annihilation i * creation j) * creationWord v by noncomm_ring]
      rw [hac]
      by_cases h : i = j
      · subst j
        simp only [ite_true, mul_one]
        rw [ih v ht]
        simp
      · simp [h]

/-- Actual same-degree prefix creation ranges are orthogonal for all Fock vectors. -/
theorem orthogonal_creationWordFamily (n : ℕ) :
    OrthogonalFamily ℂ (fun _ : Fin n → I => WordSpace I)
      (fun a => creationWordIsometry (List.ofFn a)) := by
  intro a b hab f g
  change inner ℂ (creationWord (List.ofFn a) f) (creationWord (List.ofFn b) g) = 0
  rw [← ContinuousLinearMap.adjoint_inner_right]
  have he : (creationWord (List.ofFn a)).adjoint * creationWord (List.ofFn b) = 0 := by
    have h := annihilationWord_reverse_creationWord (List.ofFn a) (List.ofFn b)
      (by simp)
    have hne : List.ofFn a ≠ List.ofFn b := fun h => hab (List.ofFn_injective h)
    simpa only [hne, ite_false, ← star_creationWord, ContinuousLinearMap.star_eq_adjoint] using h
  have ha := congrArg (fun T : WordSpace I →L[ℂ] WordSpace I => T g) he
  change inner ℂ f (((creationWord (List.ofFn a)).adjoint * creationWord (List.ofFn b)) g) = 0
  rw [ha]
  simp

end FreeProbability.Fock

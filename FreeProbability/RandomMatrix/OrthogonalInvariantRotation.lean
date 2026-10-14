import FreeProbability.RandomMatrix.OrthogonalInvariantCoefficients

/-! # Exact fresh-color splitting under genuine normalized plane mixing -/

noncomputable section
open scoped Classical
namespace FreeProbability.Orthogonal
open Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Sites carrying the color to be split. -/
abbrev ColorSites {k : ℕ} (i : Fin k → n) (c : n) := {a : Fin k // i a = c}

/-- The actual tuple obtained by choosing one of the two colors at each split site. -/
def colorSplitTuple {k : ℕ} (i : Fin k → n) (c d : n) (γ : ColorSites i c → Bool) : Fin k → n :=
  fun a => if h : i a = c then if γ ⟨a, h⟩ then d else c else i a

/-- Exactly the tuple support of the mixer kernel when the second color is fresh. -/
def ColorSplitAllowed {k : ℕ} (i : Fin k → n) (c d : n) (j : Fin k → n) : Prop :=
  ∀ a, if i a = c then j a = c ∨ j a = d else j a = i a

omit [Fintype n] in
private theorem colorSplitTuple_allowed {k : ℕ} (i : Fin k → n) (c d : n)
    (γ : ColorSites i c → Bool) : ColorSplitAllowed i c d (colorSplitTuple i c d γ) := by
  intro a
  by_cases h : i a = c
  · simp only [h, ite_true, colorSplitTuple, dite_eq_left]
    cases γ ⟨a, h⟩ <;> simp
  · simp [h, colorSplitTuple]

/-- A genuine finite equivalence between split choices and all allowed tuples. -/
def colorSplitEquiv {k : ℕ} (i : Fin k → n) (c d : n) (hcd : c ≠ d) :
    (ColorSites i c → Bool) ≃ {j : Fin k → n // ColorSplitAllowed i c d j} where
  toFun γ := ⟨colorSplitTuple i c d γ, colorSplitTuple_allowed i c d γ⟩
  invFun j a := decide (j.1 a.1 = d)
  left_inv γ := by
    funext a
    simp only [colorSplitTuple, a.2, dite_eq_left]
    cases γ a <;> simp [hcd]
  right_inv j := by
    apply Subtype.ext
    funext a
    have hj := j.2 a
    by_cases h : i a = c
    · simp only [h, ite_true] at hj
      rcases hj with hc | hd
      · simp [colorSplitTuple, h, hc, hcd]
      · simp [colorSplitTuple, h, hd]
    · simp only [h, ite_false] at hj
      simp [colorSplitTuple, h, hj]

omit [Fintype n] in
private theorem planeMixer_product_kernel {k : ℕ} (i j : Fin k → n) (c d : n)
    (hcd : c ≠ d) (hfresh : ∀ a, i a ≠ d) (q : ℝ) :
    (∏ a : Fin k, planeMixerMatrix c d q (i a) (j a)) =
      if ColorSplitAllowed i c d j then q ^ (Finset.univ.filter (fun a => i a = c)).card else 0 := by
  by_cases hj : ColorSplitAllowed i c d j
  · simp only [hj, ite_true]
    have he (a : Fin k) : planeMixerMatrix c d q (i a) (j a) = if i a = c then q else 1 := by
      have ha := hj a
      by_cases hc : i a = c
      · simp only [hc, ite_true] at ha
        rcases ha with he | he <;> simp [planeMixerMatrix, hc, he, hcd, Ne.symm hcd]
      · simp only [hc, ite_false] at ha
        simp [planeMixerMatrix, hc, hfresh a, ha]
    simp_rw [he]
    simp [Finset.prod_ite]
  · simp only [hj, ite_false]
    obtain ⟨a, ha⟩ : ∃ a : Fin k, ¬ (if i a = c then j a = c ∨ j a = d else j a = i a) := by
      exact not_forall.mp hj
    apply Finset.prod_eq_zero (Finset.mem_univ a)
    by_cases hc : i a = c
    · simp only [hc, ite_true, not_or] at ha
      simp [planeMixerMatrix, hc, Ne.symm ha.1, Ne.symm ha.2]
    · simp only [hc, ite_false] at ha
      simp [planeMixerMatrix, hc, hfresh a, Ne.symm ha]

/-- Actual plane mixing splits a color block over ALL Boolean choices at its
sites, with the exact normalized weight and no assumed coefficient relation. -/
theorem tensorPower_planeMixer_fresh_coefficient {k : ℕ}
    (v : EuclideanSpace ℝ (Fin k → n)) (i : Fin k → n) (c d : n)
    (hcd : c ≠ d) (hfresh : ∀ a, i a ≠ d) :
    ((tensorPowerRepresentation (n := n) k).action (planeMixer c d hcd) v) i =
      ((Real.sqrt 2)⁻¹) ^ (Finset.univ.filter (fun a => i a = c)).card *
        ∑ γ : ColorSites i c → Bool, v (colorSplitTuple i c d γ) := by
  rw [tensorPower_action_coefficient]
  change (∑ j : Fin k → n, (∏ a : Fin k,
    planeMixerMatrix c d ((Real.sqrt 2)⁻¹) (i a) (j a)) * v j) = _
  simp_rw [planeMixer_product_kernel i _ c d hcd hfresh, ite_mul, zero_mul]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero]
  rw [← Finset.sum_subtype_eq_sum_filter]
  have hs := (colorSplitEquiv i c d hcd).sum_comp
    (fun j : {j : Fin k → n // ColorSplitAllowed i c d j} => v j.1)
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.subtype_univ]
  exact hs.symm

/-- ACTUAL fixedness gives the exact fresh-color block-splitting recurrence. -/
theorem invariantTensor_fresh_color_split {k : ℕ} (v : EuclideanSpace ℝ (Fin k → n))
    (hv : v ∈ (tensorPowerRepresentation (n := n) k).fixedVectors)
    (i : Fin k → n) (c d : n) (hcd : c ≠ d) (hfresh : ∀ a, i a ≠ d) :
    v i = ((Real.sqrt 2)⁻¹) ^ (Finset.univ.filter (fun a => i a = c)).card *
      ∑ γ : ColorSites i c → Bool, v (colorSplitTuple i c d γ) := by
  have he := congrArg (fun w : EuclideanSpace ℝ (Fin k → n) => w i) (hv (planeMixer c d hcd))
  rw [tensorPower_planeMixer_fresh_coefficient v i c d hcd hfresh] at he
  exact he.symm
end FreeProbability.Orthogonal

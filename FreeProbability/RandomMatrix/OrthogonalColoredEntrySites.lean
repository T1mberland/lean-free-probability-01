import FreeProbability.RandomMatrix.OrthogonalColoredEntryWeingarten

/-! # Genuine regrouping of arbitrary colored entry sites -/

noncomputable section
open scoped Classical
namespace FreeProbability.Orthogonal
open Matrix MeasureTheory ProbabilityTheory
variable {Ω I S n : Type*} [MeasurableSpace Ω] [Fintype I] [Fintype S] [Fintype n] [DecidableEq n]

/-- The actual sites of one color, including an empty fiber. -/
abbrev ColoredEntrySites (color : S → I) (c : I) := {a : S // color a = c}

/-- An actual bijective enumeration of a color fiber; its degree is its TRUE cardinality. -/
def coloredEntrySiteEnumeration (color : S → I) (c : I) :
    Fin (Fintype.card (ColoredEntrySites color c)) ≃ ColoredEntrySites color c :=
  (Fintype.equivFin _).symm

/-- The original row or column label restricted to the actual fiber enumeration. -/
def coloredEntryLocalLabels (color : S → I) (i : S → n) (c : I) :
    Fin (Fintype.card (ColoredEntrySites color c)) → n :=
  fun k => i (coloredEntrySiteEnumeration color c k).val

/-- The genuine entry product in arbitrary original site order. Color labels
may repeat nonadjacently and no order or evenness premise is imposed. -/
def coloredSiteMonomial (color : S → I) (i j : S → n) (U : I → Group n) : ℝ :=
  ∏ a, U (color a) (i a) (j a)

/-- Original sites really regroup into the actual color fibers and their
bijective Fin enumerations. No reordering identity is supplied as a premise. -/
theorem coloredSiteMonomial_eq_grouped (color : S → I) (i j : S → n) (U : I → Group n) :
    coloredSiteMonomial color i j U =
      ∏ c, entryMonomial (coloredEntryLocalLabels color i c) (coloredEntryLocalLabels color j c) (U c) := by
  have he : coloredSiteMonomial color i j U =
      ∏ c, ∏ a : ColoredEntrySites color c, U c (i a.val) (j a.val) := by
    unfold coloredSiteMonomial
    rw [← (Equiv.sigmaFiberEquiv color).prod_comp, Fintype.prod_sigma]
    apply Finset.prod_congr rfl
    intro c _
    apply Finset.prod_congr rfl
    intro a _
    change U (color a.val) (i a.val) (j a.val) = U c (i a.val) (j a.val)
    rw [a.property]
  rw [he]
  apply Finset.prod_congr rfl
  intro c _
  exact (coloredEntrySiteEnumeration color c).prod_comp (fun a => U c (i a.val) (j a.val)) |>.symm

/-- True original-site entry integral for independent actual Haar colors. -/
theorem coloredSiteIntegral_eq_product (μ : Measure Ω) (X : I → Ω → Group n)
    (color : S → I) (i j : S → n) (hi : iIndepFun X μ)
    (hX : ∀ c, MeasurePreserving (X c) μ (haar n)) :
    (∫ ω, coloredSiteMonomial color i j (fun c => X c ω) ∂μ) =
      ∏ c, entryMoment (coloredEntryLocalLabels color i c) (coloredEntryLocalLabels color j c) := by
  have he : (fun ω => coloredSiteMonomial color i j (fun c => X c ω)) =
      coloredEntryMonomial X (coloredEntryLocalLabels color i) (coloredEntryLocalLabels color j) := by
    funext ω
    exact coloredSiteMonomial_eq_grouped color i j _
  rw [he]
  exact coloredEntryIntegral_eq_product μ X _ _ hi hX

/-- An odd number of ACTUAL sites of any color kills the original-site integral. -/
theorem coloredSiteIntegral_eq_zero_of_odd (μ : Measure Ω) (X : I → Ω → Group n)
    (color : S → I) (i j : S → n) (hi : iIndepFun X μ)
    (hX : ∀ c, MeasurePreserving (X c) μ (haar n))
    (c : I) (hc : Odd (Fintype.card (ColoredEntrySites color c))) :
    (∫ ω, coloredSiteMonomial color i j (fun c => X c ω) ∂μ) = 0 := by
  rw [coloredSiteIntegral_eq_product μ X color i j hi hX]
  exact Finset.prod_eq_zero (Finset.mem_univ c)
    (entryMoment_eq_zero_of_odd _ _ hc)

/-- Original-site colored monomials are genuinely integrable under the
actual independent Haar law. -/
theorem integrable_coloredSiteMonomial (μ : Measure Ω) (X : I → Ω → Group n)
    (color : S → I) (i j : S → n) (hi : iIndepFun X μ)
    (hX : ∀ c, MeasurePreserving (X c) μ (haar n)) :
    Integrable (fun ω => coloredSiteMonomial color i j (fun c => X c ω)) μ := by
  convert integrable_coloredEntryMonomial μ X
    (coloredEntryLocalLabels color i) (coloredEntryLocalLabels color j) hi hX using 1
  funext ω
  exact coloredSiteMonomial_eq_grouped color i j _

/-- Original site labels on an even color fiber, using the true fiber degree. -/
def coloredEntryEvenLabels (color : S → I) (i : S → n) (r : I → ℕ)
    (hc : ∀ c, Fintype.card (ColoredEntrySites color c) = 2 * r c) (c : I) : Fin (2 * r c) → n :=
  fun k => coloredEntryLocalLabels color i c ((finCongr (hc c)).symm k)

/-- The actual integral in original site order equals the true color-respecting
pairing sum whenever every actual color fiber has even stable degree. -/
theorem coloredSiteIntegral_eq_weingarten_sum (μ : Measure Ω) (X : I → Ω → Group n)
    (color : S → I) (i j : S → n) (hi : iIndepFun X μ)
    (hX : ∀ c, MeasurePreserving (X c) μ (haar n)) (r : I → ℕ)
    (hc : ∀ c, Fintype.card (ColoredEntrySites color c) = 2 * r c)
    (hr : ∀ c, r c ≤ Fintype.card n) :
    (∫ ω, coloredSiteMonomial color i j (fun c => X c ω) ∂μ) =
      ∑ p : (∀ c, OrdinaryPairing (r c)), ∑ q : (∀ c, OrdinaryPairing (r c)),
        ∏ c, ordinaryPairingDelta (p c) (coloredEntryEvenLabels color i r hc c) *
          (ordinaryPairingGram n (r c))⁻¹ (p c) (q c) *
          ordinaryPairingDelta (q c) (coloredEntryEvenLabels color j r hc c) := by
  have hm (c : I) (U : Group n) :
      entryMonomial (coloredEntryLocalLabels color i c) (coloredEntryLocalLabels color j c) U =
      entryMonomial (coloredEntryEvenLabels color i r hc c) (coloredEntryEvenLabels color j r hc c) U :=
    ((finCongr (hc c)).symm.prod_comp
      (fun k => U (coloredEntryLocalLabels color i c k) (coloredEntryLocalLabels color j c k))).symm
  have he : (fun ω => coloredSiteMonomial color i j (fun c => X c ω)) =
      coloredEntryMonomial X (coloredEntryEvenLabels color i r hc) (coloredEntryEvenLabels color j r hc) := by
    funext ω
    rw [coloredSiteMonomial_eq_grouped]
    unfold coloredEntryMonomial
    exact Finset.prod_congr rfl (fun c _ => hm c _)
  rw [he]
  exact coloredEntryIntegral_eq_weingarten_sum μ X _ _ hi hX hr

end FreeProbability.Orthogonal

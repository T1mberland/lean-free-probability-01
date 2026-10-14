import FreeProbability.RandomMatrix.OrthogonalColoredEntryIntegration

/-! # Genuine color-dependent Weingarten integration -/

noncomputable section
open scoped Classical
namespace FreeProbability.Orthogonal
open Matrix MeasureTheory ProbabilityTheory
variable {Ω I n : Type*} [MeasurableSpace Ω] [Fintype I] [Fintype n] [DecidableEq n]
variable (μ : Measure Ω) (X : I → Ω → Group n)

/-- True per-color stable integration yields the actual product of genuine
one-color inverse-Gram pairing sums, with all degrees zero included. -/
theorem coloredEntryIntegral_eq_weingarten_product {r : I → ℕ}
    (i j : ∀ c, Fin (2 * r c) → n) (hi : iIndepFun X μ)
    (hX : ∀ c, MeasurePreserving (X c) μ (haar n)) (hr : ∀ c, r c ≤ Fintype.card n) :
    coloredEntryIntegral μ X i j = ∏ c, ∑ p : OrdinaryPairing (r c), ∑ q : OrdinaryPairing (r c),
      ordinaryPairingDelta p (i c) * (ordinaryPairingGram n (r c))⁻¹ p q * ordinaryPairingDelta q (j c) := by
  rw [coloredEntryIntegral_eq_product μ X i j hi hX]
  apply Finset.prod_congr rfl
  intro c _
  exact entryMoment_eq_weingarten_delta_sum (hr c) (i c) (j c)

/-- The actual colored Haar entry integral is a double sum over genuine
color-respecting pairing choices, with the product of actual inverse weights. -/
theorem coloredEntryIntegral_eq_weingarten_sum {r : I → ℕ}
    (i j : ∀ c, Fin (2 * r c) → n) (hi : iIndepFun X μ)
    (hX : ∀ c, MeasurePreserving (X c) μ (haar n)) (hr : ∀ c, r c ≤ Fintype.card n) :
    coloredEntryIntegral μ X i j =
      ∑ p : (∀ c, OrdinaryPairing (r c)), ∑ q : (∀ c, OrdinaryPairing (r c)),
        ∏ c, ordinaryPairingDelta (p c) (i c) * (ordinaryPairingGram n (r c))⁻¹ (p c) (q c) *
          ordinaryPairingDelta (q c) (j c) := by
  rw [coloredEntryIntegral_eq_weingarten_product μ X i j hi hX hr, Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro p _
  exact Fintype.prod_sum _

end FreeProbability.Orthogonal

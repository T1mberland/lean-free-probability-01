import FreeProbability.Fock.SecondQuantizationPrefixOperators

/-! # Complete Hilbert amplification and literal double commutants -/

noncomputable section
open scoped Classical ENNReal
namespace FreeProbability.Fock
variable {A E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A genuine matrix block of an arbitrary bounded operator on the complete Hilbert sum. -/
def hilbertSumOperatorBlock (Q : ConstantHilbertSum A E →L[ℂ] ConstantHilbertSum A E)
    (a b : A) : E →L[ℂ] E :=
  (lp.evalCLM ℂ (fun _ : A => E) 2 a).comp
    (Q.comp (lp.singleContinuousLinearMap ℂ (fun _ : A => E) 2 b))

/-- Commutation with an amplified operator forces every actual matrix block to commute. -/
theorem hilbertSumOperatorBlock_commutes
    (Q : ConstantHilbertSum A E →L[ℂ] ConstantHilbertSum A E) (S : E →L[ℂ] E)
    (h : hilbertAmplification S * Q = Q * hilbertAmplification S) (a b : A) :
    S * hilbertSumOperatorBlock Q a b = hilbertSumOperatorBlock Q a b * S := by
  apply ContinuousLinearMap.ext
  intro x
  have hx := congrArg (fun R : ConstantHilbertSum A E →L[ℂ] ConstantHilbertSum A E =>
    R (lp.single 2 b x) a) h
  simp only [mul_apply_eq_comp, hilbertAmplification_apply,
    hilbertAmplification_single] at hx
  exact hx

/-- Blockwise commutation implies commutation on every infinite Hilbert-sum vector. -/
theorem hilbertAmplification_commutes_of_blocks
    (Q : ConstantHilbertSum A E →L[ℂ] ConstantHilbertSum A E) (T : E →L[ℂ] E)
    (h : ∀ a b, T * hilbertSumOperatorBlock Q a b = hilbertSumOperatorBlock Q a b * T) :
    hilbertAmplification T * Q = Q * hilbertAmplification T := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro b
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext a
  have hx := congrArg (fun R : E →L[ℂ] E => R x) (h a b)
  simp only [mul_apply_eq_comp] at hx
  change T (Q (lp.single 2 b x) a) = Q (hilbertAmplification T (lp.single 2 b x)) a
  rw [hilbertAmplification_single]
  exact hx

/-- Actual amplification preserves literal algebraic double commutants. -/
theorem hilbertAmplification_mem_doubleCentralizer (s : Set (E →L[ℂ] E))
    {T : E →L[ℂ] E} (hT : T ∈ Set.centralizer (Set.centralizer s)) :
    hilbertAmplification (A := A) T ∈
      Set.centralizer (Set.centralizer (hilbertAmplification (A := A) '' s)) := by
  intro Q hQ
  symm
  apply hilbertAmplification_commutes_of_blocks
  intro a b
  symm
  apply hT
  intro S hS
  exact hilbertSumOperatorBlock_commutes Q S (hQ _ ⟨S, hS, rfl⟩) a b

end FreeProbability.Fock

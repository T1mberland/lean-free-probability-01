import FreeProbability.Fock.SecondQuantizationSuffixCompression

/-! # Full prefix amplification commutes with outside right creators and annihilators -/
noncomputable section
open scoped Classical ENNReal
namespace FreeProbability.Fock
variable {I J : Type*}

/-- Appending an outside letter changes only the tail coordinate. -/
def prefixTailAppendOutside (t : PrefixTail I J) (j : J) : PrefixTail I J :=
  match t with
  | none => some (j, [])
  | some (k, w) => some (k, w ++ [Sum.inr j])

theorem joinPrefixTail_appendOutside (w : List I) (t : PrefixTail I J) (j : J) :
    joinPrefixTail (w, prefixTailAppendOutside t j) = joinPrefixTail (w, t) ++ [Sum.inr j] := by
  cases t with
  | none => simp [joinPrefixTail, prefixTailAppendOutside, prefixTailWord]
  | some t => obtain ⟨k, v⟩ := t; simp [joinPrefixTail, prefixTailAppendOutside, prefixTailWord, List.append_assoc]

/-- Actual right creation by an outside letter shifts tails on EVERY complete prefix sector. -/
theorem rightCreation_outside_prefixTail_comp (t : PrefixTail I J) (j : J) :
    (rightCreation (Sum.inr j)).comp (prefixTailEmbedding t).toContinuousLinearMap =
      (prefixTailEmbedding (prefixTailAppendOutside t j)).toContinuousLinearMap := by
  apply lp.ext_continuousLinearMap (ENNReal.ofNat_ne_top (n := 2))
  intro w
  apply ContinuousLinearMap.ext
  intro c
  have hs : lp.single 2 w c = c • word w := by
    apply lp.ext
    funext v
    simp [word, lp.single_apply, Pi.single_apply]
  change rightCreation (Sum.inr j) (prefixTailEmbedding t (lp.single 2 w c)) =
    prefixTailEmbedding (prefixTailAppendOutside t j) (lp.single 2 w c)
  rw [hs, map_smul, map_smul, identification_prefixTailEmbedding_word, rightCreation_word]
  rw [map_smul, identification_prefixTailEmbedding_word, joinPrefixTail_appendOutside]

/-- Equality on every complete tail sector determines a bounded operator on all doubled Fock space. -/
theorem prefixTailSector_ext (F G : WordSpace (Sum I J) →L[ℂ] WordSpace (Sum I J))
    (h : ∀ t (f : WordSpace I), F (prefixTailEmbedding t f) = G (prefixTailEmbedding t f)) : F = G := by
  have hc : F.comp prefixTailDecomposition.symm.toLinearIsometry.toContinuousLinearMap =
      G.comp prefixTailDecomposition.symm.toLinearIsometry.toContinuousLinearMap := by
    apply lp.ext_continuousLinearMap (ENNReal.ofNat_ne_top (n := 2))
    intro t
    apply ContinuousLinearMap.ext
    intro f
    change F (prefixTailDecomposition.symm (lp.single 2 t f)) =
      G (prefixTailDecomposition.symm (lp.single 2 t f))
    rw [prefixTailDecomposition_symm_single]
    exact h t f
  apply ContinuousLinearMap.ext
  intro f
  have hf := DFunLike.congr_fun hc (prefixTailDecomposition f)
  change F (prefixTailDecomposition.symm (prefixTailDecomposition f)) =
    G (prefixTailDecomposition.symm (prefixTailDecomposition f)) at hf
  simpa only [LinearIsometryEquiv.symm_apply_apply] using hf

/-- No commutant assumption on T: every amplified prefix operator commutes with outside right creation. -/
theorem prefixOperatorEmbedding_commute_rightCreation_outside
    (T : WordSpace I →L[ℂ] WordSpace I) (j : J) :
    Commute (prefixOperatorEmbedding T) (rightCreation (Sum.inr j)) := by
  apply prefixTailSector_ext
  intro t f
  change prefixOperatorEmbedding T (rightCreation (Sum.inr j) (prefixTailEmbedding t f)) =
    rightCreation (Sum.inr j) (prefixOperatorEmbedding T (prefixTailEmbedding t f))
  have h := DFunLike.congr_fun (rightCreation_outside_prefixTail_comp t j) f
  change rightCreation (Sum.inr j) (prefixTailEmbedding t f) =
    prefixTailEmbedding (prefixTailAppendOutside t j) f at h
  rw [h, prefixOperatorEmbedding_sector, prefixOperatorEmbedding_sector]
  exact (DFunLike.congr_fun (rightCreation_outside_prefixTail_comp t j) (T f)).symm

/-- Actual Hilbert adjoints give outside right-annihilation commutation on the whole completed space. -/
theorem prefixOperatorEmbedding_commute_rightAnnihilation_outside
    (T : WordSpace I →L[ℂ] WordSpace I) (j : J) :
    Commute (prefixOperatorEmbedding T) (rightAnnihilation (Sum.inr j)) := by
  have h := congrArg star (prefixOperatorEmbedding_commute_rightCreation_outside (star T) j).eq
  simp only [star_mul, map_star, star_star] at h
  exact h.symm

end FreeProbability.Fock

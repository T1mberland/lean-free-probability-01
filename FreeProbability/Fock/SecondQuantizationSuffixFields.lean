import FreeProbability.Fock.SecondQuantizationSuffixWords

/-! # Complete-sector right-field action and source-commutant suffix transport -/
noncomputable section
open scoped Classical ENNReal
namespace FreeProbability.Fock
variable {I J : Type*}

private theorem suffixSourceCLM_ext_word {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F G : WordSpace I →L[ℂ] E) (h : ∀ w, F (word w) = G (word w)) : F = G := by
  apply lp.ext_continuousLinearMap (ENNReal.ofNat_ne_top (n := 2))
  intro w
  apply ContinuousLinearMap.ext
  intro c
  have hs : lp.single 2 w c = c • word w := by
    apply lp.ext
    funext v
    simp [word, lp.single_apply, Pi.single_apply]
  change F (lp.single 2 w c) = G (lp.single 2 w c)
  rw [hs, map_smul, map_smul, h]

theorem rightSemicircular_prefixEmpty_comp (i : I) :
    (rightSemicircular (Sum.inl i)).comp (prefixTailEmbedding (J := J) none).toContinuousLinearMap =
      (prefixTailEmbedding none).toContinuousLinearMap.comp (rightSemicircular i) := by
  apply suffixSourceCLM_ext_word
  intro w
  change rightSemicircular (Sum.inl i) (prefixTailEmbedding none (word w)) =
    prefixTailEmbedding none (rightSemicircular i (word w))
  rw [identification_prefixTailEmbedding_word]
  simp only [joinPrefixTail, prefixTailWord, List.append_nil]
  cases w using List.reverseRecOn with
  | nil =>
    rw [List.map_nil, rightSemicircular_word_nil, rightSemicircular_word_nil,
      identification_prefixTailEmbedding_word]
    rfl
  | append_singleton v j =>
    rw [List.map_append, List.map_singleton, rightSemicircular_word_append,
      rightSemicircular_word_append, map_add, identification_prefixTailEmbedding_word]
    by_cases h : i = j <;> simp [h, joinPrefixTail, prefixTailWord, List.map_append,
      identification_prefixTailEmbedding_word]

theorem rightSemicircular_prefixOutside_nil_comp (i : I) (j : J) :
    (rightSemicircular (Sum.inl i)).comp (prefixTailEmbedding (some (j, []))).toContinuousLinearMap =
      (prefixTailEmbedding (some (j, [Sum.inl i]))).toContinuousLinearMap := by
  apply suffixSourceCLM_ext_word
  intro w
  change rightSemicircular (Sum.inl i) (prefixTailEmbedding (some (j, [])) (word w)) =
    prefixTailEmbedding (some (j, [Sum.inl i])) (word w)
  rw [identification_prefixTailEmbedding_word, identification_prefixTailEmbedding_word]
  change rightSemicircular (Sum.inl i) (word (w.map Sum.inl ++ [Sum.inr j])) = _
  rw [rightSemicircular_word_append]
  simp [joinPrefixTail, prefixTailWord]

theorem rightSemicircular_prefixOutside_append_comp (i : I) (j : J)
    (v : List (Sum I J)) (a : Sum I J) :
    (rightSemicircular (Sum.inl i)).comp (prefixTailEmbedding (some (j, v ++ [a]))).toContinuousLinearMap =
      (prefixTailEmbedding (some (j, v ++ [a, Sum.inl i]))).toContinuousLinearMap +
        if Sum.inl i = a then (prefixTailEmbedding (some (j, v))).toContinuousLinearMap else 0 := by
  apply suffixSourceCLM_ext_word
  intro w
  change rightSemicircular (Sum.inl i) (prefixTailEmbedding (some (j, v ++ [a])) (word w)) = _
  rw [identification_prefixTailEmbedding_word]
  have hj : joinPrefixTail (w, some (j, v ++ [a])) =
      (w.map Sum.inl ++ Sum.inr j :: v) ++ [a] := by
    simp [joinPrefixTail, prefixTailWord, List.append_assoc]
  rw [hj, rightSemicircular_word_append]
  by_cases h : Sum.inl i = a <;> simp [h, identification_prefixTailEmbedding_word,
    joinPrefixTail, prefixTailWord, List.append_assoc]

/-- Source right-field commutation extends to the included right field on ALL complete tail sectors. -/
theorem prefixOperatorEmbedding_commute_rightSemicircular (T : WordSpace I →L[ℂ] WordSpace I)
    (i : I) (hT : Commute T (rightSemicircular i)) :
    Commute (prefixOperatorEmbedding (J := J) T) (rightSemicircular (Sum.inl i)) := by
  apply prefixTailSector_ext
  intro t f
  change prefixOperatorEmbedding T (rightSemicircular (Sum.inl i) (prefixTailEmbedding t f)) =
    rightSemicircular (Sum.inl i) (prefixOperatorEmbedding T (prefixTailEmbedding t f))
  rw [prefixOperatorEmbedding_sector]
  cases t with
  | none =>
    have h1 := DFunLike.congr_fun (rightSemicircular_prefixEmpty_comp (J := J) i) f
    have h2 := DFunLike.congr_fun (rightSemicircular_prefixEmpty_comp (J := J) i) (T f)
    change rightSemicircular (Sum.inl i) (prefixTailEmbedding none f) =
      prefixTailEmbedding none (rightSemicircular i f) at h1
    change rightSemicircular (Sum.inl i) (prefixTailEmbedding none (T f)) =
      prefixTailEmbedding none (rightSemicircular i (T f)) at h2
    rw [h1, h2, prefixOperatorEmbedding_sector]
    exact congrArg (prefixTailEmbedding none) (DFunLike.congr_fun hT.eq f)
  | some t =>
    obtain ⟨j, v⟩ := t
    cases v using List.reverseRecOn with
    | nil =>
      have h1 := DFunLike.congr_fun (rightSemicircular_prefixOutside_nil_comp i j) f
      have h2 := DFunLike.congr_fun (rightSemicircular_prefixOutside_nil_comp i j) (T f)
      change rightSemicircular (Sum.inl i) (prefixTailEmbedding (some (j, [])) f) =
        prefixTailEmbedding (some (j, [Sum.inl i])) f at h1
      change rightSemicircular (Sum.inl i) (prefixTailEmbedding (some (j, [])) (T f)) =
        prefixTailEmbedding (some (j, [Sum.inl i])) (T f) at h2
      rw [h1, h2, prefixOperatorEmbedding_sector]
    | append_singleton v a =>
      have h1 := DFunLike.congr_fun (rightSemicircular_prefixOutside_append_comp i j v a) f
      have h2 := DFunLike.congr_fun (rightSemicircular_prefixOutside_append_comp i j v a) (T f)
      by_cases h : Sum.inl i = a
      · rw [ite_eq_left h] at h1 h2
        change rightSemicircular (Sum.inl i) (prefixTailEmbedding (some (j, v ++ [a])) f) =
          prefixTailEmbedding (some (j, v ++ [a, Sum.inl i])) f + prefixTailEmbedding (some (j, v)) f at h1
        change rightSemicircular (Sum.inl i) (prefixTailEmbedding (some (j, v ++ [a])) (T f)) =
          prefixTailEmbedding (some (j, v ++ [a, Sum.inl i])) (T f) + prefixTailEmbedding (some (j, v)) (T f) at h2
        rw [h1, h2, map_add, prefixOperatorEmbedding_sector, prefixOperatorEmbedding_sector]
      · rw [ite_eq_right h] at h1 h2
        change rightSemicircular (Sum.inl i) (prefixTailEmbedding (some (j, v ++ [a])) f) =
          prefixTailEmbedding (some (j, v ++ [a, Sum.inl i])) f + 0 at h1
        change rightSemicircular (Sum.inl i) (prefixTailEmbedding (some (j, v ++ [a])) (T f)) =
          prefixTailEmbedding (some (j, v ++ [a, Sum.inl i])) (T f) + 0 at h2
        rw [add_zero] at h1 h2
        rw [h1, h2, prefixOperatorEmbedding_sector]

theorem wordReversalUnitary_conj_rightSemicircular (i : I) :
    wordReversalUnitary.conjStarAlgEquiv (rightSemicircular i) = semicircular i := by
  rw [← wordReversalUnitary_conj_semicircular, wordReversalUnitary_conj_involutive]

/-- Actual source field-commutant operators extend by suffix amplification to the included field commutant. -/
theorem wordSuffixEmbedding_commute_semicircular (T : WordSpace I →L[ℂ] WordSpace I)
    (i : I) (hT : Commute T (semicircular i)) :
    Commute (wordSuffixEmbedding (J := J) T) (semicircular (Sum.inl i)) := by
  have h := congrArg wordReversalUnitary.conjStarAlgEquiv hT.eq
  rw [map_mul, map_mul, wordReversalUnitary_conj_semicircular] at h
  have hp := congrArg wordReversalUnitary.conjStarAlgEquiv
    (prefixOperatorEmbedding_commute_rightSemicircular (J := J)
      (wordReversalUnitary.conjStarAlgEquiv T) i h).eq
  rw [map_mul, map_mul, wordReversalUnitary_conj_rightSemicircular] at hp
  exact hp

end FreeProbability.Fock

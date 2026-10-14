import FreeProbability.Fock.SecondQuantizationSuffixOrthogonal

/-! # Unconditional creator commutator is exactly the empty-tail source defect -/
noncomputable section
open scoped Classical InnerProductSpace ENNReal
namespace FreeProbability.Fock
variable {I J : Type*}

private theorem suffixDefect_ext_word {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
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

/-- The adjoint of empty-tail inclusion selects exactly that complete orthogonal sector. -/
theorem prefixEmpty_adjoint_sector (t : PrefixTail I J) (f : WordSpace I) :
    (prefixTailEmbedding none).toContinuousLinearMap.adjoint (prefixTailEmbedding t f) =
      if t = none then f else 0 := by
  by_cases ht : t = none
  · subst t
    rw [ite_eq_left rfl]
    exact DFunLike.congr_fun (prefixTailEmbedding (I := I) (J := J) none).adjoint_comp_self f
  · rw [ite_eq_right ht]
    apply ext_inner_left ℂ
    intro g
    rw [ContinuousLinearMap.adjoint_inner_right, inner_zero_right]
    exact orthogonal_prefixTailEmbedding (i := none) (j := t) (fun h => ht h.symm) g f

theorem rightCreation_prefixEmpty_comp (i : I) :
    (rightCreation (Sum.inl i)).comp (prefixTailEmbedding (J := J) none).toContinuousLinearMap =
      (prefixTailEmbedding none).toContinuousLinearMap.comp (rightCreation i) := by
  apply suffixDefect_ext_word
  intro w
  change rightCreation (Sum.inl i) (prefixTailEmbedding none (word w)) =
    prefixTailEmbedding none (rightCreation i (word w))
  rw [identification_prefixTailEmbedding_word, rightCreation_word, rightCreation_word,
    identification_prefixTailEmbedding_word]
  simp [joinPrefixTail, prefixTailWord, List.map_append]

theorem rightCreation_prefixOutside_comp (i : I) (j : J) (v : List (Sum I J)) :
    (rightCreation (Sum.inl i)).comp (prefixTailEmbedding (some (j, v))).toContinuousLinearMap =
      (prefixTailEmbedding (some (j, v ++ [Sum.inl i]))).toContinuousLinearMap := by
  apply suffixDefect_ext_word
  intro w
  change rightCreation (Sum.inl i) (prefixTailEmbedding (some (j, v)) (word w)) =
    prefixTailEmbedding (some (j, v ++ [Sum.inl i])) (word w)
  rw [identification_prefixTailEmbedding_word, rightCreation_word, identification_prefixTailEmbedding_word]
  simp [joinPrefixTail, prefixTailWord, List.append_assoc]

/-- Exact unconditional source creator defect, supported on the empty-tail sector only. -/
theorem prefixOperatorEmbedding_rightCreation_defect (T : WordSpace I →L[ℂ] WordSpace I) (i : I) :
    prefixOperatorEmbedding (J := J) T * rightCreation (Sum.inl i) -
      rightCreation (Sum.inl i) * prefixOperatorEmbedding T =
    (prefixTailEmbedding none).toContinuousLinearMap.comp
      ((T * rightCreation i - rightCreation i * T).comp
        (prefixTailEmbedding none).toContinuousLinearMap.adjoint) := by
  apply prefixTailSector_ext
  intro t f
  change prefixOperatorEmbedding T (rightCreation (Sum.inl i) (prefixTailEmbedding t f)) -
    rightCreation (Sum.inl i) (prefixOperatorEmbedding T (prefixTailEmbedding t f)) =
      prefixTailEmbedding none ((T * rightCreation i - rightCreation i * T)
        ((prefixTailEmbedding none).toContinuousLinearMap.adjoint (prefixTailEmbedding t f)))
  rw [prefixOperatorEmbedding_sector, prefixEmpty_adjoint_sector]
  cases t with
  | none =>
    rw [ite_eq_left rfl]
    have h1 := DFunLike.congr_fun (rightCreation_prefixEmpty_comp (J := J) i) f
    have h2 := DFunLike.congr_fun (rightCreation_prefixEmpty_comp (J := J) i) (T f)
    change rightCreation (Sum.inl i) (prefixTailEmbedding none f) =
      prefixTailEmbedding none (rightCreation i f) at h1
    change rightCreation (Sum.inl i) (prefixTailEmbedding none (T f)) =
      prefixTailEmbedding none (rightCreation i (T f)) at h2
    rw [h1, h2, prefixOperatorEmbedding_sector]
    exact (map_sub (prefixTailEmbedding none) (T (rightCreation i f)) (rightCreation i (T f))).symm
  | some t =>
    obtain ⟨j, v⟩ := t
    rw [ite_eq_right (by simp), map_zero, map_zero]
    have h1 := DFunLike.congr_fun (rightCreation_prefixOutside_comp i j v) f
    have h2 := DFunLike.congr_fun (rightCreation_prefixOutside_comp i j v) (T f)
    change rightCreation (Sum.inl i) (prefixTailEmbedding (some (j, v)) f) =
      prefixTailEmbedding (some (j, v ++ [Sum.inl i])) f at h1
    change rightCreation (Sum.inl i) (prefixTailEmbedding (some (j, v)) (T f)) =
      prefixTailEmbedding (some (j, v ++ [Sum.inl i])) (T f) at h2
    rw [h1, h2, prefixOperatorEmbedding_sector, sub_self]

end FreeProbability.Fock

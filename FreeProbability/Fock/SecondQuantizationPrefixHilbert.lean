import FreeProbability.Fock.SecondQuantizationPrefixWords

/-! # Full Hilbert prefix/tail decomposition, including infinite amplitudes -/
noncomputable section
open scoped Classical InnerProductSpace
namespace FreeProbability.Fock
variable {I J : Type*}

abbrev PrefixTailHilbert (I J : Type*) := lp (fun _ : PrefixTail I J => ↥(WordSpace I)) 2

theorem orthonormal_prefixTail (t : PrefixTail I J) :
    Orthonormal ℂ (fun w : List I => word (joinPrefixTail (w, t))) := by
  rw [orthonormal_iff_ite]
  intro w v
  rw [inner_word]
  have he : joinPrefixTail (w, t) = joinPrefixTail (v, t) ↔ w = v := by
    constructor
    · intro h
      exact congrArg Prod.fst ((prefixTailEquiv I J).symm.injective h)
    · rintro rfl; rfl
  simp only [he]

/-- The complete prefix amplitudes with one fixed outside-starting tail. -/
def prefixTailEmbedding (t : PrefixTail I J) : WordSpace I →ₗᵢ[ℂ] WordSpace (Sum I J) :=
  (orthonormal_prefixTail t).orthogonalFamily.linearIsometry

@[simp] theorem prefixTailEmbedding_single (t : PrefixTail I J) (w : List I) (c : ℂ) :
    prefixTailEmbedding t (lp.single 2 w c) = c • word (joinPrefixTail (w, t)) := by
  rw [prefixTailEmbedding, OrthogonalFamily.linearIsometry_apply_single]
  simp [LinearIsometry.toSpanSingleton_apply]

theorem hasSum_prefixTailEmbedding (t : PrefixTail I J) (f : WordSpace I) :
    HasSum (fun w => f w • word (joinPrefixTail (w, t))) (prefixTailEmbedding t f) := by
  simpa only [prefixTailEmbedding, LinearIsometry.toSpanSingleton_apply] using
    (orthonormal_prefixTail t).orthogonalFamily.hasSum_linearIsometry f

/-- Distinct tails give orthogonal closed copies of the whole included Fock space. -/
theorem orthogonal_prefixTailEmbedding :
    OrthogonalFamily ℂ (fun _ : PrefixTail I J => ↥(WordSpace I)) (fun t => prefixTailEmbedding t) := by
  intro t s hts f g
  have hword (w : List I) : inner ℂ (word (joinPrefixTail (w, t))) (prefixTailEmbedding s g) = 0 := by
    have hs := (innerSL ℂ (word (joinPrefixTail (w, t)))).hasSum (hasSum_prefixTailEmbedding s g)
    have ht (v : List I) :
        inner ℂ (word (joinPrefixTail (w, t))) (g v • word (joinPrefixTail (v, s))) = 0 := by
      have hne : joinPrefixTail (w, t) ≠ joinPrefixTail (v, s) := by
        intro h
        exact hts (congrArg Prod.snd ((prefixTailEquiv I J).symm.injective h))
      rw [inner_smul_right, inner_word]
      simp only [hne, ite_false, mul_zero]
    simp only [innerSL_apply_apply, ht] at hs
    exact hs.unique hasSum_zero
  have hs := (innerSL ℂ (prefixTailEmbedding s g)).hasSum (hasSum_prefixTailEmbedding t f)
  have ht (w : List I) :
      inner ℂ (prefixTailEmbedding s g) (f w • word (joinPrefixTail (w, t))) = 0 := by
    rw [inner_smul_right, ← inner_conj_symm, hword]
    simp
  simp only [innerSL_apply_apply, ht] at hs
  rw [← inner_conj_symm, hs.unique hasSum_zero]
  simp

theorem prefixTailEmbedding_total :
    ⊤ ≤ (⨆ t : PrefixTail I J, LinearMap.range (prefixTailEmbedding t).toLinearMap).topologicalClosure := by
  let b : HilbertBasis (List (Sum I J)) ℂ (WordSpace (Sum I J)) :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ (WordSpace (Sum I J)))
  have hb : (b : List (Sum I J) → WordSpace (Sum I J)) = word := by
    funext w
    apply b.repr.injective
    rw [b.repr_self]
    change lp.single 2 w 1 = (LinearIsometryEquiv.refl ℂ (WordSpace (Sum I J))) (word w)
    apply lp.ext
    funext v
    simp [word, lp.single_apply, Pi.single_apply]
  have hd : (Submodule.span ℂ (Set.range (word : List (Sum I J) → WordSpace (Sum I J)))).topologicalClosure = ⊤ := by
    rw [← hb]
    exact b.dense_span
  rw [← hd]
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_le.mpr
  rintro _ ⟨w, rfl⟩
  apply le_iSup (fun t : PrefixTail I J => LinearMap.range (prefixTailEmbedding t).toLinearMap)
    (splitPrefixTail w).2
  refine ⟨lp.single 2 (splitPrefixTail w).1 (1 : ℂ), ?_⟩
  change prefixTailEmbedding (splitPrefixTail w).2 (lp.single 2 (splitPrefixTail w).1 (1 : ℂ)) = word w
  rw [prefixTailEmbedding_single, one_smul, join_splitPrefixTail]

theorem prefixTail_isHilbertSum :
    IsHilbertSum ℂ (fun _ : PrefixTail I J => ↥(WordSpace I)) (fun t => prefixTailEmbedding t) :=
  IsHilbertSum.mk orthogonal_prefixTailEmbedding prefixTailEmbedding_total

/-- Genuine full-space unitary onto the complete Hilbert sum of prefix copies. -/
def prefixTailDecomposition : WordSpace (Sum I J) ≃ₗᵢ[ℂ] PrefixTailHilbert I J :=
  prefixTail_isHilbertSum.linearIsometryEquiv

@[simp] theorem prefixTailDecomposition_symm_single (t : PrefixTail I J) (f : WordSpace I) :
    prefixTailDecomposition.symm (lp.single 2 t f) = prefixTailEmbedding t f :=
  prefixTail_isHilbertSum.linearIsometryEquiv_symm_apply_single f

end FreeProbability.Fock

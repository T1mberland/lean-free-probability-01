import FreeProbability.Fock.HilbertBasisModel

/-!
# The Hilbert direct-sum decomposition by word length

Each fixed-length level is a genuine complete square-summable Hilbert space.
The word Fock space is isometrically equivalent to their Hilbert direct sum.
Identifying these levels with completed Hilbert tensor powers is still separate.
-/

noncomputable section
open scoped Classical InnerProductSpace

namespace FreeProbability.Fock

variable {I : Type*}

/-- The complete Hilbert space of amplitudes on words of length `n`. -/
abbrev WordLevel (I : Type*) (n : ℕ) := lp (fun _ : Fin n → I => ℂ) 2

/-- The external Hilbert direct sum of all complete length levels. -/
abbrev GradedWordSpace (I : Type*) := lp (fun n => ↥(WordLevel I n)) 2

theorem orthonormal_fixedLength (n : ℕ) :
    Orthonormal ℂ (fun a : Fin n → I => word (List.ofFn a)) := by
  rw [orthonormal_iff_ite]
  intro a b
  rw [inner_word]
  simp only [List.ofFn_injective.eq_iff]

/-- Canonical isometric inclusion of a complete length level into Fock space. -/
def levelEmbedding (n : ℕ) : WordLevel I n →ₗᵢ[ℂ] WordSpace I :=
  (orthonormal_fixedLength n).orthogonalFamily.linearIsometry

@[simp] theorem levelEmbedding_single (n : ℕ) (a : Fin n → I) (c : ℂ) :
    levelEmbedding n (lp.single 2 a c) = c • word (List.ofFn a) := by
  rw [levelEmbedding, OrthogonalFamily.linearIsometry_apply_single]
  simp [LinearIsometry.toSpanSingleton_apply]

theorem hasSum_levelEmbedding (n : ℕ) (f : WordLevel I n) :
    HasSum (fun a => f a • word (List.ofFn a)) (levelEmbedding n f) := by
  simpa only [levelEmbedding, LinearIsometry.toSpanSingleton_apply] using
    (orthonormal_fixedLength n).orthogonalFamily.hasSum_linearIsometry f

/-- Distinct length levels are orthogonal, including infinite amplitudes. -/
theorem orthogonal_levelEmbedding :
    OrthogonalFamily ℂ (fun n => ↥(WordLevel I n)) (fun n => levelEmbedding n) := by
  intro n m hnm f g
  have hword (a : Fin n → I) : inner ℂ (word (List.ofFn a)) (levelEmbedding m g) = 0 := by
    have hs := (innerSL ℂ (word (List.ofFn a))).hasSum (hasSum_levelEmbedding m g)
    have ht (b : Fin m → I) : inner ℂ (word (List.ofFn a)) (g b • word (List.ofFn b)) = 0 := by
      have hne : List.ofFn a ≠ List.ofFn b := by
        intro h
        exact hnm (by simpa using congrArg List.length h)
      rw [inner_smul_right, inner_word]; simp only [hne, ite_false, mul_zero]
    simp only [innerSL_apply_apply, ht] at hs
    exact hs.unique hasSum_zero
  have hs := (innerSL ℂ (levelEmbedding m g)).hasSum (hasSum_levelEmbedding n f)
  have ht (a : Fin n → I) : inner ℂ (levelEmbedding m g) (f a • word (List.ofFn a)) = 0 := by
    rw [inner_smul_right, ← inner_conj_symm, hword]
    simp
  simp only [innerSL_apply_apply, ht] at hs
  rw [← inner_conj_symm, hs.unique hasSum_zero]
  simp

/-- Every Fock vector is in the closed span of the actual length levels. -/
theorem levelEmbedding_total :
    ⊤ ≤ (⨆ n, LinearMap.range (levelEmbedding (I := I) n).toLinearMap).topologicalClosure := by
  have hd : (Submodule.span ℂ (Set.range (word : List I → WordSpace I))).topologicalClosure = ⊤ := by
    let b : HilbertBasis (List I) ℂ (WordSpace I) :=
      HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ (WordSpace I))
    have hb : (b : List I → WordSpace I) = word := by
      funext w
      apply b.repr.injective
      rw [b.repr_self]
      change lp.single 2 w 1 = (LinearIsometryEquiv.refl ℂ (WordSpace I)) (word w)
      simp [word]
    rw [← hb]
    exact b.dense_span
  rw [← hd]
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_le.mpr
  rintro _ ⟨w, rfl⟩
  apply (le_iSup (fun n => LinearMap.range (levelEmbedding (I := I) n).toLinearMap) w.length)
  refine ⟨lp.single 2 w.get (1 : ℂ), ?_⟩
  change levelEmbedding w.length (lp.single 2 w.get (1 : ℂ)) = word w
  rw [levelEmbedding_single, one_smul, List.ofFn_get]

/-- The complete word Fock space is genuinely the Hilbert sum of its length levels. -/
theorem wordSpace_isHilbertSum :
    IsHilbertSum ℂ (fun n => ↥(WordLevel I n)) (fun n => levelEmbedding n) :=
  IsHilbertSum.mk orthogonal_levelEmbedding levelEmbedding_total

/-- The genuine Hilbert grading equivalence, without any finite-support restriction. -/
def lengthDecomposition : WordSpace I ≃ₗᵢ[ℂ] GradedWordSpace I :=
  wordSpace_isHilbertSum.linearIsometryEquiv

@[simp] theorem lengthDecomposition_symm_single (n : ℕ) (f : WordLevel I n) :
    lengthDecomposition.symm (lp.single 2 n f) = levelEmbedding n f :=
  wordSpace_isHilbertSum.linearIsometryEquiv_symm_apply_single f

/-- The inverse grading equivalence sums the length sectors in the Hilbert topology. -/
theorem hasSum_lengthDecomposition_symm (f : GradedWordSpace I) :
    HasSum (fun n => levelEmbedding n (f n)) (lengthDecomposition.symm f) :=
  wordSpace_isHilbertSum.hasSum_linearIsometryEquiv_symm f

end FreeProbability.Fock

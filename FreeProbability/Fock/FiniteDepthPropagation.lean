import FreeProbability.Fock.FiniteDepthProjection

/-! # Genuine finite propagation of the actual Fock field operators -/
noncomputable section
open scoped Classical InnerProductSpace
namespace FreeProbability.Fock
variable {I : Type*} [Fintype I]

/-- The actual finite-dimensional depth subspace. -/
def depthSpace (L : ℕ) : Submodule ℂ (WordSpace I) :=
  Submodule.span ℂ (word '' (depthWords (I := I) L : Set (List I)))

theorem word_mem_depthSpace {L : ℕ} (w : List I) (hw : w.length ≤ L) :
    word w ∈ depthSpace L :=
  Submodule.subset_span ⟨w, (mem_depthWords L w).mpr hw, rfl⟩

theorem depthSpace_mono {L M : ℕ} (h : L ≤ M) : depthSpace (I := I) L ≤ depthSpace M := by
  apply Submodule.span_mono
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨w, (mem_depthWords M w).mpr (((mem_depthWords L w).mp hw).trans h), rfl⟩

theorem creation_word_mem_depthSpace (i : I) (L : ℕ) (w : List I) (hw : w.length ≤ L) :
    creation i (word w) ∈ depthSpace (L + 1) := by
  rw [creation_word]
  exact word_mem_depthSpace _ (by simpa using Nat.succ_le_succ hw)

theorem annihilation_word_mem_depthSpace (i : I) (L : ℕ) (w : List I) (hw : w.length ≤ L) :
    annihilation i (word w) ∈ depthSpace (L + 1) := by
  rw [annihilation_word]
  cases w with
  | nil => exact Submodule.zero_mem _
  | cons j w =>
    change (if i = j then word w else 0) ∈ depthSpace (L + 1)
    split_ifs
    · exact word_mem_depthSpace _ (by simp only [List.length_cons] at hw; omega)
    · exact Submodule.zero_mem _

/-- The actual semicircular field preserves the claimed depth bound on every vector in the depth space. -/
theorem semicircular_mem_depthSpace (i : I) (L : ℕ) {f : WordSpace I} (hf : f ∈ depthSpace L) :
    semicircular i f ∈ depthSpace (L + 1) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨w, hw, rfl⟩ := hf
    change creation i (word w) + annihilation i (word w) ∈ depthSpace (L + 1)
    exact Submodule.add_mem _ (creation_word_mem_depthSpace i L w ((mem_depthWords L w).mp hw))
      (annihilation_word_mem_depthSpace i L w ((mem_depthWords L w).mp hw))
  | zero => simpa only [map_zero] using (Submodule.zero_mem (depthSpace (I := I) (L + 1)))
  | add f g _ _ hf hg => rw [map_add]; exact Submodule.add_mem _ hf hg
  | smul c f _ hf => rw [map_smul]; exact Submodule.smul_mem _ c hf

/-- The literal depth projection fixes exactly the actual depth subspace. -/
theorem depthProjection_eq_self_iff (L : ℕ) (f : WordSpace I) :
    depthProjection L f = f ↔ f ∈ depthSpace L := by
  unfold depthSpace
  rw [← depthProjection_range]
  constructor
  · intro h; exact ⟨f, h⟩
  · rintro ⟨g, rfl⟩
    exact DFunLike.congr_fun (depthProjection_idempotent L) g

end FreeProbability.Fock

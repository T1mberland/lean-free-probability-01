import FreeProbability.Fock.SecondQuantizationPrefixOperators

/-! # Full completed word-space unitary for arbitrary alphabet equivalences -/
noncomputable section
open scoped Classical InnerProductSpace ENNReal
namespace FreeProbability.Fock
variable {I J : Type*}

theorem orthonormal_reindexedWords (e : I ≃ J) :
    Orthonormal ℂ (fun w : List I => word (w.map e)) := by
  rw [orthonormal_iff_ite]
  intro w v
  rw [inner_word]
  have he : w.map e = v.map e ↔ w = v := by
    constructor
    · intro h
      have hh := congrArg (List.map e.symm) h
      simpa [List.map_map, Function.comp_def] using hh
    · rintro rfl; rfl
  simp only [he]

theorem reindexedWords_total (e : I ≃ J) :
    ⊤ ≤ (Submodule.span ℂ (Set.range (fun w : List I => word (w.map e)))).topologicalClosure := by
  let S := Submodule.span ℂ (Set.range (fun w : List I => word (w.map e)))
  intro f _
  have hword (w : List J) : word w ∈ S := by
    have hh : (w.map e.symm).map e = w := by simp [List.map_map, Function.comp_def]
    rw [← hh]
    exact Submodule.subset_span (Set.mem_range_self (w.map e.symm))
  have hs : ∀ q : Finset (List J), ∑ w ∈ q, lp.single 2 w (f w) ∈ S.topologicalClosure := by
    intro q
    apply S.topologicalClosure.sum_mem
    intro w _
    apply S.le_topologicalClosure
    have hh : (lp.single 2 w (f w) : WordSpace J) = f w • word w := by
      apply lp.ext
      funext v
      simp [word, lp.single_apply, Pi.single_apply]
    rw [hh]
    exact S.smul_mem _ (hword w)
  exact S.isClosed_topologicalClosure.mem_of_tendsto
    (lp.hasSum_single (ENNReal.ofNat_ne_top (n := 2)) f) (Filter.Eventually.of_forall hs)

/-- Actual complete Hilbert basis after arbitrary reindexing of word letters. -/
def reindexedWordBasis (e : I ≃ J) : HilbertBasis (List I) ℂ (WordSpace J) :=
  HilbertBasis.mk (orthonormal_reindexedWords e) (reindexedWords_total e)

/-- Genuine onto unitary on all square-summable word amplitudes. -/
def wordAlphabetUnitary (e : I ≃ J) : WordSpace I ≃ₗᵢ[ℂ] WordSpace J :=
  (reindexedWordBasis e).repr.symm

@[simp] theorem wordAlphabetUnitary_word (e : I ≃ J) (w : List I) :
    wordAlphabetUnitary e (word w) = word (w.map e) := by
  have hh : word w = lp.single 2 w (1 : ℂ) := by
    apply lp.ext
    funext v
    simp [word, lp.single_apply, Pi.single_apply]
  rw [hh]
  change (reindexedWordBasis e).repr.symm (lp.single 2 w 1) = _
  rw [HilbertBasis.repr_symm_single]
  exact congrFun (HilbertBasis.coe_mk (orthonormal_reindexedWords e) (reindexedWords_total e)) w

end FreeProbability.Fock

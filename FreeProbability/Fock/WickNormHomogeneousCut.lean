import FreeProbability.Fock.WickNormMatrixCut
import FreeProbability.Fock.WickProductTupleSplit
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-! # Every homogeneous Wick coefficient cut has the actual Hilbert square-sum norm bound -/

noncomputable section
open scoped Classical

namespace FreeProbability.Fock

variable {I : Type*}

/-- Embed fixed-degree word coefficients into their exact prefix/reversed-suffix matrix. -/
def wickCoefficientMatrix (p q : ℕ) (c : (Fin (p + q) → I) →₀ ℂ) :
    ((Fin p → I) × (Fin q → I)) →₀ ℂ :=
  c.embDomain ⟨wickTupleSplit p q, wickTupleSplit_injective p q⟩

/-- The actual normal-order cut of a finite homogeneous coefficient family. -/
def homogeneousWickCut (p q : ℕ) (c : (Fin (p + q) → I) →₀ ℂ) :
    WordSpace I →L[ℂ] WordSpace I :=
  c.sum fun a z => z •
    (creationWord ((List.ofFn a).take p) * annihilationWord ((List.ofFn a).drop p))

/-- Every finite homogeneous coefficient cut has norm bounded by the original coefficient ℓ² norm. -/
theorem norm_homogeneousWickCut_le (p q : ℕ) (c : (Fin (p + q) → I) →₀ ℂ) :
    ‖homogeneousWickCut p q c‖ ≤ Real.sqrt (c.sum fun _ z => ‖z‖ ^ 2) := by
  let g := wickCoefficientMatrix p q c
  let s := g.support.image Prod.fst
  let t := g.support.image Prod.snd
  have hs : g.support ⊆ s.product t := by
    intro x hx
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem Prod.fst hx, Finset.mem_image_of_mem Prod.snd hx⟩
  have he : wickCreatorMatrixCut p q s t (fun u v => g (u, v)) = homogeneousWickCut p q c := by
    unfold wickCreatorMatrixCut
    rw [← Finset.sum_product (f := fun x => g x •
      (creationWord (List.ofFn x.1) * annihilationWord (List.ofFn x.2).reverse))]
    have hz : ∀ x ∈ s.product t, (0 : ℂ) •
        (creationWord (List.ofFn x.1) * annihilationWord (List.ofFn x.2).reverse) = 0 := by
      intro x hx
      apply ContinuousLinearMap.ext
      intro f
      simp
    have hh := g.sum_of_support_subset hs (fun x z => z •
      (creationWord (List.ofFn x.1) * annihilationWord (List.ofFn x.2).reverse)) hz
    apply hh.symm.trans
    change (c.embDomain ⟨wickTupleSplit p q, wickTupleSplit_injective p q⟩).sum _ = _
    rw [Finsupp.sum_embDomain]
    apply Finsupp.sum_congr
    intro a ha
    change c a • (creationWord (List.ofFn (wickTupleSplit p q a).1) *
      annihilationWord (List.ofFn (wickTupleSplit p q a).2).reverse) = _
    rw [ofFn_wickTupleSplit_fst, ofFn_wickTupleSplit_snd_reverse]
  have hn : (∑ u ∈ s, ∑ v ∈ t, ‖g (u, v)‖ ^ 2) = c.sum (fun _ z => ‖z‖ ^ 2) := by
    rw [← Finset.sum_product (f := fun x => ‖g x‖ ^ 2)]
    have hh := g.sum_of_support_subset hs (fun _ z => ‖z‖ ^ 2) (by simp)
    apply hh.symm.trans
    change (c.embDomain ⟨wickTupleSplit p q, wickTupleSplit_injective p q⟩).sum _ = _
    simp only [Finsupp.sum_embDomain]
  rw [← he, ← hn]
  exact norm_wickCreatorMatrixCut_le p q s t (fun u v => g (u, v))

end FreeProbability.Fock

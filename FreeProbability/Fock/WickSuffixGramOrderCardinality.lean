import FreeProbability.Fock.WickSuffixGramOrderCoefficient
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.Pi

/-! # Exact finite-alphabet suffix-fiber counts, including empty alphabets -/
noncomputable section
open scoped Classical
namespace FreeProbability.Fock
variable {I : Type*} [Fintype I]

/-- A fixed suffix fiber injects into the complete set of length-h prefixes. -/
theorem suffixFiber_card_le (S : Finset (List I)) (h : ℕ) (s : List I)
    (hl : ∀ u ∈ S, h ≤ u.length) :
    (S.filter (fun u => u.drop h = s)).card ≤ (Fintype.card I) ^ h := by
  let F := S.filter (fun u => u.drop h = s)
  let P := Finset.univ.image (List.ofFn : (Fin h → I) → List I)
  have hm : Set.MapsTo (List.take h) (F : Set (List I)) (P : Set (List I)) := by
    intro u hu
    have hlen : (u.take h).length = h := by
      simp [List.length_take, Nat.min_eq_left (hl u (Finset.mem_filter.mp hu).1)]
    let f : Fin h → I := fun k => (u.take h)[k.val]'(by rw [hlen]; exact k.isLt)
    have he : List.ofFn f = u.take h := by
      apply List.ext_getElem
      · simp [hlen]
      · intro i hi hj
        simp only [List.getElem_ofFn, f]
    exact Finset.mem_image.mpr ⟨f, Finset.mem_univ _, he⟩
  have hinj : (F : Set (List I)).InjOn (List.take h) := by
    intro u hu v hv hp
    have hdu := (Finset.mem_filter.mp hu).2
    have hdv := (Finset.mem_filter.mp hv).2
    rw [← List.take_append_drop h u, ← List.take_append_drop h v, hp, hdu, hdv]
  calc
    F.card ≤ P.card := Finset.card_le_card_of_injOn (List.take h) hm hinj
    _ ≤ (Finset.univ : Finset (Fin h → I)).card := Finset.card_image_le
    _ = (Fintype.card I) ^ h := by simp

end FreeProbability.Fock

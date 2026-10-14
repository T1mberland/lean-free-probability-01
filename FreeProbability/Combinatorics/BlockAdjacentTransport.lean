import FreeProbability.Combinatorics.NoncrossingDuplicateBlocks
import Mathlib.Order.Fin.Tuple

/-! # Ordered block words across adjacent duplication and fusion -/

namespace FreeProbability

variable {n : ℕ} {A : Type*} [Monoid A]

/-- Fusing an inserted entry with its right neighbor is a single-coordinate update. -/
theorem fuseAdjacent_insertNth (x : Fin n → A) (i : Fin n) (a : A) :
    fuseAdjacent (i.castSucc.insertNth a x) i = Function.update x i (a * x i) := by
  classical
  unfold fuseAdjacent
  have htail : (i.castSucc.insertNth a x) ∘ i.castSucc.succAbove = x := by
    funext j
    simp [Function.comp_apply]
  rw [htail]
  simp only [Fin.insertNth_apply_same]
  have hs : (i.castSucc.insertNth a x : Fin (n + 1) → A) i.succ = x i := by
    rw [← Fin.succAbove_castSucc_self i, Fin.insertNth_apply_succAbove]
  rw [hs]

omit [Monoid A] in
/-- The distinguished duplicated block is the original ordered block with one
entry inserted just before the selected position. -/
theorem orderedBlockWord_duplicateBlock_of_mem (x : Fin (n + 1) → A) (i : Fin n)
    (s : Finset (Fin n)) (hi : i ∈ s) :
    orderedBlockWord x (NoncrossingPartition.duplicateBlock i s) =
      List.ofFn (((s.orderIsoOfFin rfl).symm ⟨i, hi⟩).castSucc.insertNth
        (x i.castSucc) (fun a => x (i.castSucc.succAbove (s.orderEmbOfFin rfl a)))) := by
  classical
  let j := (s.orderIsoOfFin rfl).symm ⟨i, hi⟩
  let old : Fin s.card → Fin (n + 1) := i.castSucc.succAbove ∘ s.orderEmbOfFin rfl
  let g : Fin (s.card + 1) → Fin (n + 1) := j.castSucc.insertNth i.castSucc old
  have hj : s.orderEmbOfFin rfl j = i :=
    congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨i, hi⟩)
  have hmono : StrictMono g := by
    apply (Fin.strictMono_insertNth_iff _ _ _).mpr
    refine ⟨i.castSucc.succAboveOrderEmb.strictMono.comp (s.orderEmbOfFin rfl).strictMono, ?_, ?_⟩
    · intro a haj
      have ha : a < j := Fin.castSucc_lt_castSucc_iff.mp haj
      have hai : s.orderEmbOfFin rfl a < i := by
        simpa only [hj] using (s.orderEmbOfFin rfl).lt_iff_lt.mpr ha
      change i.castSucc.succAbove (s.orderEmbOfFin rfl a) < i.castSucc
      rw [Fin.succAbove_castSucc_of_lt _ _ hai]
      exact Fin.castSucc_lt_castSucc_iff.mpr hai
    · intro a hja
      have ha : j ≤ a := Fin.castSucc_le_castSucc_iff.mp hja
      have hia : i ≤ s.orderEmbOfFin rfl a := by
        simpa only [hj] using (s.orderEmbOfFin rfl).le_iff_le.mpr ha
      change i.castSucc < i.castSucc.succAbove (s.orderEmbOfFin rfl a)
      rw [Fin.succAbove_castSucc_of_le _ _ hia]
      exact lt_of_lt_of_le (Fin.castSucc_lt_succ : i.castSucc < i.succ) (Fin.succ_le_succ_iff.mpr hia)
  have hcard : (NoncrossingPartition.duplicateBlock i s).card = s.card + 1 := by
    simp only [NoncrossingPartition.card_duplicateBlock, hi, ite_true]
  have hmem (a : Fin (s.card + 1)) : g a ∈ NoncrossingPartition.duplicateBlock i s := by
    refine Fin.succAboveCases j.castSucc ?_ (fun a => ?_) a
    · simp only [g, Fin.insertNth_apply_same, NoncrossingPartition.mem_duplicateBlock,
        Fin.predAbove_castSucc_self]
      exact hi
    · simp only [g, Fin.insertNth_apply_succAbove, old, Function.comp_apply,
        NoncrossingPartition.mem_duplicateBlock, Fin.predAbove_succAbove]
      exact s.orderEmbOfFin_mem rfl a
  have hg := Finset.orderEmbOfFin_unique hcard hmem hmono
  have hword : orderedBlockWord x (NoncrossingPartition.duplicateBlock i s) = List.ofFn (x ∘ g) := by
    rw [List.ofFn_eq_map, ← List.map_map, hg,
      Finset.listMap_orderEmbOfFin_finRange]
    rfl
  rw [hword]
  congr 1
  funext a
  refine Fin.succAboveCases j.castSucc ?_ (fun a => ?_) a
  · simp [g, Function.comp_apply, j]
  · simp [g, old, Function.comp_apply, j]

/-- Fusing the distinguished block agrees exactly with reading the reduced block. -/
theorem fuseAdjacent_duplicateBlock_tuple (x : Fin (n + 1) → A) (i : Fin n)
    (s : Finset (Fin n)) (hi : i ∈ s) :
    fuseAdjacent (((s.orderIsoOfFin rfl).symm ⟨i, hi⟩).castSucc.insertNth
      (x i.castSucc) (fun a => x (i.castSucc.succAbove (s.orderEmbOfFin rfl a))))
      ((s.orderIsoOfFin rfl).symm ⟨i, hi⟩) = fuseAdjacent x i ∘ s.orderEmbOfFin rfl := by
  classical
  let j := (s.orderIsoOfFin rfl).symm ⟨i, hi⟩
  have hj : s.orderEmbOfFin rfl j = i :=
    congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨i, hi⟩)
  rw [fuseAdjacent_insertNth]
  change Function.update ((x ∘ i.castSucc.succAbove) ∘ s.orderEmbOfFin rfl) j
    (x i.castSucc * x (i.castSucc.succAbove (s.orderEmbOfFin rfl j))) =
      Function.update (x ∘ i.castSucc.succAbove) i (x i.castSucc * x i.succ) ∘ s.orderEmbOfFin rfl
  rw [hj, Fin.succAbove_castSucc_self]
  have hh := (Function.update_comp_eq_of_injective (x ∘ i.castSucc.succAbove)
    (s.orderEmbOfFin rfl).injective j (x i.castSucc * x i.succ)).symm
  rw [hj] at hh
  exact hh

/-- List form of the exact distinguished-block fusion transport. -/
theorem orderedBlockWord_fuseAdjacent_of_mem (x : Fin (n + 1) → A) (i : Fin n)
    (s : Finset (Fin n)) (hi : i ∈ s) :
    List.ofFn (fuseAdjacent (((s.orderIsoOfFin rfl).symm ⟨i, hi⟩).castSucc.insertNth
      (x i.castSucc) (fun a => x (i.castSucc.succAbove (s.orderEmbOfFin rfl a))))
      ((s.orderIsoOfFin rfl).symm ⟨i, hi⟩)) = orderedBlockWord (fuseAdjacent x i) s := by
  rw [fuseAdjacent_duplicateBlock_tuple]
  unfold orderedBlockWord
  rw [List.ofFn_eq_map, ← List.map_map, Finset.listMap_orderEmbOfFin_finRange]

end FreeProbability

import FreeProbability.Combinatorics.BlockAdjacentTransport
import FreeProbability.Combinatorics.NoncrossingReindex

/-! # Cardinality reindexing of the duplicated block and its marked positions -/

namespace FreeProbability

variable {n : ℕ}

/-- Explicit enumeration of the enlarged block, after the cardinality cast. -/
theorem duplicateBlock_enumeration (i : Fin n) (s : Finset (Fin n)) (hi : i ∈ s)
    (hcard : (NoncrossingPartition.duplicateBlock i s).card = s.card + 1) :
    (NoncrossingPartition.duplicateBlock i s).orderEmbOfFin rfl ∘ Fin.cast hcard.symm =
      ((s.orderIsoOfFin rfl).symm ⟨i, hi⟩).castSucc.insertNth i.castSucc
        (i.castSucc.succAbove ∘ s.orderEmbOfFin rfl) := by
  have h := orderedBlockWord_duplicateBlock_of_mem (fun a : Fin (n + 1) => a) i s hi
  have he : orderedBlockWord (fun a : Fin (n + 1) => a) (NoncrossingPartition.duplicateBlock i s) =
      List.ofFn ((NoncrossingPartition.duplicateBlock i s).orderEmbOfFin rfl) := by
    rw [List.ofFn_eq_map, Finset.listMap_orderEmbOfFin_finRange]
    simp [orderedBlockWord]
  rw [he, List.ofFn_congr hcard] at h
  exact List.ofFn_injective h

/-- The first marked position reindexes to the insertion index. -/
theorem duplicateBlock_left_index (i : Fin n) (s : Finset (Fin n)) (hi : i ∈ s)
    (hcard : (NoncrossingPartition.duplicateBlock i s).card = s.card + 1)
    (hl : i.castSucc ∈ NoncrossingPartition.duplicateBlock i s) :
    (Fin.castOrderIso hcard.symm).symm
      (((NoncrossingPartition.duplicateBlock i s).orderIsoOfFin rfl).symm ⟨i.castSucc, hl⟩) =
        ((s.orderIsoOfFin rfl).symm ⟨i, hi⟩).castSucc := by
  apply (Fin.castOrderIso hcard.symm).injective
  apply ((NoncrossingPartition.duplicateBlock i s).orderEmbOfFin rfl).injective
  rw [(Fin.castOrderIso hcard.symm).apply_symm_apply]
  have hpos : (NoncrossingPartition.duplicateBlock i s).orderEmbOfFin rfl
      (((NoncrossingPartition.duplicateBlock i s).orderIsoOfFin rfl).symm ⟨i.castSucc, hl⟩) =
      i.castSucc := congrArg Subtype.val
        (((NoncrossingPartition.duplicateBlock i s).orderIsoOfFin rfl).apply_symm_apply ⟨i.castSucc, hl⟩)
  rw [hpos]
  have h := congrFun (duplicateBlock_enumeration i s hi hcard)
    (((s.orderIsoOfFin rfl).symm ⟨i, hi⟩).castSucc)
  change i.castSucc = (NoncrossingPartition.duplicateBlock i s).orderEmbOfFin rfl
    (Fin.cast hcard.symm (((s.orderIsoOfFin rfl).symm ⟨i, hi⟩).castSucc))
  simpa only [Function.comp_apply, Fin.insertNth_apply_same] using h.symm

/-- The second marked position reindexes to the right neighbor of the insertion index. -/
theorem duplicateBlock_right_index (i : Fin n) (s : Finset (Fin n)) (hi : i ∈ s)
    (hcard : (NoncrossingPartition.duplicateBlock i s).card = s.card + 1)
    (hr : i.succ ∈ NoncrossingPartition.duplicateBlock i s) :
    (Fin.castOrderIso hcard.symm).symm
      (((NoncrossingPartition.duplicateBlock i s).orderIsoOfFin rfl).symm ⟨i.succ, hr⟩) =
        ((s.orderIsoOfFin rfl).symm ⟨i, hi⟩).succ := by
  let j := (s.orderIsoOfFin rfl).symm ⟨i, hi⟩
  have hj : s.orderEmbOfFin rfl j = i :=
    congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨i, hi⟩)
  apply (Fin.castOrderIso hcard.symm).injective
  apply ((NoncrossingPartition.duplicateBlock i s).orderEmbOfFin rfl).injective
  rw [(Fin.castOrderIso hcard.symm).apply_symm_apply]
  have hpos : (NoncrossingPartition.duplicateBlock i s).orderEmbOfFin rfl
      (((NoncrossingPartition.duplicateBlock i s).orderIsoOfFin rfl).symm ⟨i.succ, hr⟩) =
      i.succ := congrArg Subtype.val
        (((NoncrossingPartition.duplicateBlock i s).orderIsoOfFin rfl).apply_symm_apply ⟨i.succ, hr⟩)
  rw [hpos]
  have h := congrFun (duplicateBlock_enumeration i s hi hcard) j.succ
  rw [← Fin.succAbove_castSucc_self j, Fin.insertNth_apply_succAbove] at h
  change i.succ = (NoncrossingPartition.duplicateBlock i s).orderEmbOfFin rfl
    (Fin.cast hcard.symm j.succ)
  simpa only [Function.comp_apply, Fin.succAbove_castSucc_self, hj] using h.symm

/-- Letter tuples inherit the same cardinality reindexing as the positions. -/
theorem duplicateBlock_tuple_reindex {X : Type*} (x : Fin (n + 1) → X)
    (i : Fin n) (s : Finset (Fin n)) (hi : i ∈ s)
    (hcard : (NoncrossingPartition.duplicateBlock i s).card = s.card + 1) :
    (x ∘ (NoncrossingPartition.duplicateBlock i s).orderEmbOfFin rfl) ∘ Fin.castOrderIso hcard.symm =
      ((s.orderIsoOfFin rfl).symm ⟨i, hi⟩).castSucc.insertNth
        (x i.castSucc) (fun a => x (i.castSucc.succAbove (s.orderEmbOfFin rfl a))) := by
  let j := (s.orderIsoOfFin rfl).symm ⟨i, hi⟩
  funext a
  have h := congrFun (duplicateBlock_enumeration i s hi hcard) a
  change x ((NoncrossingPartition.duplicateBlock i s).orderEmbOfFin rfl (Fin.cast hcard.symm a)) = _
  change (NoncrossingPartition.duplicateBlock i s).orderEmbOfFin rfl (Fin.cast hcard.symm a) =
    (((s.orderIsoOfFin rfl).symm ⟨i, hi⟩).castSucc.insertNth i.castSucc
      (i.castSucc.succAbove ∘ s.orderEmbOfFin rfl) : Fin (s.card + 1) → Fin (n + 1)) a at h
  rw [h]
  refine Fin.succAboveCases j.castSucc ?_ (fun a => ?_) a
  · simp [j]
  · simp [j]

end FreeProbability

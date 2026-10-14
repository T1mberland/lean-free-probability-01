import FreeProbability.Fock.WickProductNormalOrder

/-! # The actual single-word Wick operator norm is at most its degree plus one -/

noncomputable section
open scoped Classical

namespace FreeProbability.Fock

variable {I : Type*}

local instance : Nontrivial (WordSpace I) := ⟨⟨vacuum, 0, by
  intro h
  have hn := norm_vacuum (I := I)
  rw [h, norm_zero] at hn
  norm_num at hn⟩⟩

/-- Ordered products of the actual creators are contractions. -/
theorem norm_creationWord_le (w : List I) : ‖creationWord w‖ ≤ 1 := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [creationWord_cons]
    exact (norm_mul_le _ _).trans (by simpa only [norm_creation, one_mul] using ih)

/-- Ordered products of the actual annihilators are contractions. -/
theorem norm_annihilationWord_le (w : List I) : ‖annihilationWord w‖ ≤ 1 := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [annihilationWord_cons]
    exact (norm_mul_le _ _).trans (by simpa only [norm_annihilation, one_mul] using ih)

/-- Every actual normal-order cut has bounded operator norm at most one. -/
theorem norm_wickNormalOrder_cut_le (w : List I) (k : ℕ) :
    ‖creationWord (w.take k) * annihilationWord (w.drop k)‖ ≤ 1 := by
  calc
    _ ≤ ‖creationWord (w.take k)‖ * ‖annihilationWord (w.drop k)‖ := norm_mul_le _ _
    _ ≤ 1 * 1 := mul_le_mul (norm_creationWord_le _) (norm_annihilationWord_le _)
      (norm_nonneg _) zero_le_one
    _ = 1 := one_mul _

/-- Actual bounded Wick operators satisfy the single-word Haagerup degree bound. -/
theorem norm_wick_le_length_add_one (w : List I) : ‖wick w‖ ≤ (w.length : ℝ) + 1 := by
  rw [wick_normal_order_expansion]
  calc
    _ ≤ ∑ k : Fin (w.length + 1), ‖creationWord (w.take k.val) * annihilationWord (w.drop k.val)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _ : Fin (w.length + 1), (1 : ℝ) :=
      Finset.sum_le_sum (fun k _ => norm_wickNormalOrder_cut_le w k.val)
    _ = _ := by simp

end FreeProbability.Fock

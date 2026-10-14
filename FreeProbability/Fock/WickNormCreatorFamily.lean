import FreeProbability.Fock.WickProductCreationGram

/-! # Complete word-creator Hilbert sums and actual annihilator Bessel bounds -/

noncomputable section
open scoped Classical InnerProductSpace ENNReal

namespace FreeProbability.Fock

variable {I : Type*}

/-- Orthogonal degree-`n` creator ranges combine into a genuine complete Hilbert-sum isometry. -/
def creationWordFamilyIsometry (n : ℕ) :
    lp (fun _ : Fin n → I => WordSpace I) 2 →ₗᵢ[ℂ] WordSpace I :=
  (orthogonal_creationWordFamily n).linearIsometry

/-- Every complete degree-`n` Hilbert-sum coordinate is inserted by its actual word creator. -/
@[simp] theorem creationWordFamily_single (n : ℕ) (a : Fin n → I) (f : WordSpace I) :
    creationWordFamilyIsometry n (lp.single 2 a f) = creationWord (List.ofFn a) f := by
  rw [creationWordFamilyIsometry, OrthogonalFamily.linearIsometry_apply_single]
  rfl

/-- The full creator Hilbert-sum map is a contraction, including empty index sets. -/
theorem norm_creationWordFamily_le (n : ℕ) :
    ‖(creationWordFamilyIsometry (I := I) n).toContinuousLinearMap‖ ≤ 1 := by
  exact (creationWordFamilyIsometry (I := I) n).norm_toContinuousLinearMap_le

/-- Every adjoint Hilbert-sum coordinate is the actual reversed word annihilator. -/
theorem creationWordFamily_adjoint_coordinate (n : ℕ) (a : Fin n → I) (f : WordSpace I) :
    ((creationWordFamilyIsometry n).toContinuousLinearMap.adjoint f) a =
      annihilationWord (List.ofFn a).reverse f := by
  apply ext_inner_left ℂ
  intro g
  let F := (creationWordFamilyIsometry (I := I) n).toContinuousLinearMap
  have ha : (creationWord (List.ofFn a)).adjoint = annihilationWord (List.ofFn a).reverse := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using star_creationWord (List.ofFn a)
  calc
    inner ℂ g ((F.adjoint f) a) = inner ℂ (lp.single 2 a g) (F.adjoint f) :=
      (lp.inner_single_left (𝕜 := ℂ) a g (F.adjoint f)).symm
    _ = inner ℂ (F (lp.single 2 a g)) f := ContinuousLinearMap.adjoint_inner_right _ _ _
    _ = inner ℂ (creationWord (List.ofFn a) g) f := by
      change inner ℂ (creationWordFamilyIsometry n (lp.single 2 a g)) f = _
      rw [creationWordFamily_single]
    _ = inner ℂ g ((creationWord (List.ofFn a)).adjoint f) :=
      (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
    _ = _ := by rw [ha]

/-- The complete adjoint Hilbert-sum norm is bounded by the original Fock norm. -/
theorem norm_creationWordFamily_adjoint_apply_le (n : ℕ) (f : WordSpace I) :
    ‖(creationWordFamilyIsometry (I := I) n).toContinuousLinearMap.adjoint f‖ ≤ ‖f‖ := by
  calc
    _ ≤ ‖(creationWordFamilyIsometry (I := I) n).toContinuousLinearMap.adjoint‖ * ‖f‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖f‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      rw [ContinuousLinearMap.adjoint.norm_map]
      exact norm_creationWordFamily_le n
    _ = _ := one_mul _

/-- Actual finite Bessel inequality for all degree-`n` annihilator words and arbitrary Fock vectors. -/
theorem sum_norm_annihilationWord_sq_le (n : ℕ) (s : Finset (Fin n → I)) (f : WordSpace I) :
    ∑ a ∈ s, ‖annihilationWord (List.ofFn a).reverse f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  have h := lp.sum_rpow_le_norm_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    ((creationWordFamilyIsometry (I := I) n).toContinuousLinearMap.adjoint f) s
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, creationWordFamily_adjoint_coordinate] at h
  exact h.trans (pow_le_pow_left₀ (norm_nonneg _) (norm_creationWordFamily_adjoint_apply_le n f) 2)

end FreeProbability.Fock

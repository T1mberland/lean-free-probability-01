import FreeProbability.Fock.OrnsteinUhlenbeckFamilyCyclicBasis

/-! Actual original-family cyclic OU agrees on ALL vectors with original-index word-length damping. -/
noncomputable section
open scoped Classical InnerProductSpace ENNReal
namespace FreeProbability.Fock
variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Actual contractive degree damping on completed original-index word space. -/
def familyWordDegreeDamping (t : ℝ) (ht : 0 ≤ t) : WordSpace I →L[ℂ] WordSpace I :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨fun w => degreeWeight t w.length • f w, (lp.memℓp f).mono' (by
        intro w
        rw [norm_smul]
        exact (mul_le_mul_of_nonneg_right (norm_degreeWeight_le_one t ht w.length) (norm_nonneg _)).trans_eq
          (one_mul _))⟩
      map_add' := by intro f g; apply lp.ext; funext w; exact smul_add _ _ _
      map_smul' := by
        intro c f; apply lp.ext; funext w
        change degreeWeight t w.length • (c • f w) = c • (degreeWeight t w.length • f w)
        exact smul_comm _ _ _ }
    1 (by
      intro f
      change ‖(⟨fun w => degreeWeight t w.length • f w, _⟩ : WordSpace I)‖ ≤ 1 * ‖f‖
      rw [one_mul]
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro w
      change ‖degreeWeight t w.length • f w‖ ≤ ‖f w‖
      rw [norm_smul]
      exact (mul_le_mul_of_nonneg_right (norm_degreeWeight_le_one t ht w.length) (norm_nonneg _)).trans_eq
        (one_mul _))

@[simp] theorem familyWordDegreeDamping_degree (t : ℝ) (ht : 0 ≤ t) (f : WordSpace I) (w : List I) :
    familyWordDegreeDamping t ht f w = degreeWeight t w.length • f w := rfl

@[simp] theorem familyWordDegreeDamping_word (t : ℝ) (ht : 0 ≤ t) (w : List I) :
    familyWordDegreeDamping t ht (word w) = degreeWeight t w.length • word w := by
  apply lp.ext
  funext v
  change degreeWeight t v.length • (word w : WordSpace I) v =
    degreeWeight t w.length • (word w : WordSpace I) v
  by_cases hv : v = w
  · subst v; rfl
  · simp [word, lp.single_apply, hv]

/-- Genuine original-family cyclic Wick word eigenvectors with their exact original word degree. -/
theorem familyOUL2_familyCyclicWord (e : I → H) (he : Orthonormal ℂ e) (t : ℝ) (ht : 0 ≤ t) (w : List I) :
    familyOUL2 e he t ht (familyCyclicWord e w) = degreeWeight t w.length • familyCyclicWord e w := by
  apply Subtype.ext
  exact degreeDamping_familyClosedWick_vacuum e t ht w

/-- Exact whole-space unitary intertwining, beyond finite words or polynomial vacuum vectors. -/
theorem familyCyclicWordUnitary_damping_comp (e : I → H) (he : Orthonormal ℂ e) (t : ℝ) (ht : 0 ≤ t) :
    (familyOUL2 e he t ht).comp (familyCyclicWordUnitary e he).toLinearIsometry.toContinuousLinearMap =
      (familyCyclicWordUnitary e he).toLinearIsometry.toContinuousLinearMap.comp
        (familyWordDegreeDamping t ht) := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  apply ContinuousLinearMap.ext
  intro c
  change familyOUL2 e he t ht (familyCyclicWordUnitary e he (lp.single 2 w c)) =
    familyCyclicWordUnitary e he (familyWordDegreeDamping t ht (lp.single 2 w c))
  have hs : (lp.single 2 w c : WordSpace I) = c • word w := by
    apply lp.ext
    funext v
    simp [word, lp.single_apply, Pi.single_apply]
  rw [hs, map_smul, map_smul, map_smul, map_smul, familyCyclicWordUnitary_word,
    familyOUL2_familyCyclicWord, familyWordDegreeDamping_word, map_smul, familyCyclicWordUnitary_word]

/-- Every actual cyclic vector has the true OU coefficient multiplier in the original family word basis. -/
theorem familyOUL2_word_coefficient (e : I → H) (he : Orthonormal ℂ e) (t : ℝ) (ht : 0 ≤ t)
    (f : familyCyclicSpace e) (w : List I) :
    (familyCyclicWordUnitary e he).symm (familyOUL2 e he t ht f) w =
      degreeWeight t w.length • (familyCyclicWordUnitary e he).symm f w := by
  have h := DFunLike.congr_fun (familyCyclicWordUnitary_damping_comp e he t ht)
    ((familyCyclicWordUnitary e he).symm f)
  change familyOUL2 e he t ht
    (familyCyclicWordUnitary e he ((familyCyclicWordUnitary e he).symm f)) =
      familyCyclicWordUnitary e he (familyWordDegreeDamping t ht ((familyCyclicWordUnitary e he).symm f)) at h
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  have hs := congrArg (familyCyclicWordUnitary e he).symm h
  rw [LinearIsometryEquiv.symm_apply_apply] at hs
  exact congrArg (fun g : WordSpace I => g w) hs

end FreeProbability.Fock

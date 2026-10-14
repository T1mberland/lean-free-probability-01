import FreeProbability.Fock.OrnsteinUhlenbeckFamilyCyclicBasisCoefficients

/-! Actual complete adapted-word embedding and left/right original-field intertwining. -/
noncomputable section
open scoped Classical InnerProductSpace ENNReal
namespace FreeProbability.Fock
variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Actual isometric embedding of original-family completed words in the full adapted model. -/
def familyCyclicAdaptedIsometry {e : I → H} (d : OrthonormalFamilyExtension e) (he : Orthonormal ℂ e) :
    WordSpace I →ₗᵢ[ℂ] d.Space :=
  d.tensorTransport.symm.toLinearIsometry.comp
    ((familyCyclicSpace e).subtypeₗᵢ.comp (familyCyclicWordUnitary e he).toLinearIsometry)

@[simp] theorem familyCyclicAdaptedIsometry_word {e : I → H} (d : OrthonormalFamilyExtension e)
    (he : Orthonormal ℂ e) (w : List I) :
    familyCyclicAdaptedIsometry d he (word w) = word (w.map d.index) := by
  change d.tensorTransport.symm (familyCyclicWordUnitary e he (word w) : TensorFullFock H) = _
  rw [familyCyclicWordUnitary_word, familyCyclicWord_transport d]
  exact d.tensorTransport.symm_apply_apply _

 theorem familyCyclicAdaptedIsometry_tensor {e : I → H} (d : OrthonormalFamilyExtension e)
    (he : Orthonormal ℂ e) (f : WordSpace I) :
    d.tensorTransport (familyCyclicAdaptedIsometry d he f) =
      (familyCyclicWordUnitary e he f : TensorFullFock H) :=
  d.tensorTransport.apply_symm_apply _

private theorem familyCyclicAdapted_field_ext {e : I → H} (d : OrthonormalFamilyExtension e)
    (he : Orthonormal ℂ e) (A : WordSpace I →L[ℂ] WordSpace I) (B : d.Space →L[ℂ] d.Space)
    (h : ∀ w : List I, familyCyclicAdaptedIsometry d he (A (word w)) =
      B (familyCyclicAdaptedIsometry d he (word w))) :
    (familyCyclicAdaptedIsometry d he).toContinuousLinearMap.comp A =
      B.comp (familyCyclicAdaptedIsometry d he).toContinuousLinearMap := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  apply ContinuousLinearMap.ext
  intro c
  change familyCyclicAdaptedIsometry d he (A (lp.single 2 w c)) =
    B (familyCyclicAdaptedIsometry d he (lp.single 2 w c))
  have hs : (lp.single 2 w c : WordSpace I) = c • word w := by
    apply lp.ext
    funext v
    simp [word, lp.single_apply, Pi.single_apply]
  rw [hs, map_smul, map_smul, map_smul, map_smul]
  exact congrArg (c • ·) (h w)

/-- Genuine canonical left fields intertwine through the complete original-family adapted embedding. -/
theorem familyCyclicAdaptedIsometry_left_comp {e : I → H} (d : OrthonormalFamilyExtension e)
    (he : Orthonormal ℂ e) (i : I) :
    (familyCyclicAdaptedIsometry d he).toContinuousLinearMap.comp (semicircular i) =
      (semicircular (d.index i)).comp (familyCyclicAdaptedIsometry d he).toContinuousLinearMap := by
  apply familyCyclicAdapted_field_ext d he
  intro w
  cases w with
  | nil => simp [semicircular, creation_word, annihilation_word, familyCyclicAdaptedIsometry_word]
  | cons j w =>
    by_cases hij : i = j <;>
      simp [semicircular, creation_word, annihilation_word, familyCyclicAdaptedIsometry_word,
        map_add, hij, d.index_injective.eq_iff]

/-- Genuine canonical right fields intertwine through that same complete adapted embedding. -/
theorem familyCyclicAdaptedIsometry_right_comp {e : I → H} (d : OrthonormalFamilyExtension e)
    (he : Orthonormal ℂ e) (i : I) :
    (familyCyclicAdaptedIsometry d he).toContinuousLinearMap.comp (rightSemicircular i) =
      (rightSemicircular (d.index i)).comp (familyCyclicAdaptedIsometry d he).toContinuousLinearMap := by
  apply familyCyclicAdapted_field_ext d he
  intro w
  induction w using List.reverseRecOn with
  | nil => simp [rightSemicircular_word_nil, familyCyclicAdaptedIsometry_word]
  | append_singleton w j _ =>
    by_cases hij : i = j <;>
      simp [rightSemicircular_word_append, familyCyclicAdaptedIsometry_word, map_add, hij,
        d.index_injective.eq_iff, List.map_append]

end FreeProbability.Fock

import FreeProbability.Fock.SecondQuantizationPrefixAmplification

/-! # Actual included-letter bounded-operator embedding through prefix/tail sectors -/
noncomputable section
open scoped Classical InnerProductSpace ENNReal
namespace FreeProbability.Fock
variable {A E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
@[simp] theorem hilbertAmplification_single [DecidableEq A] (T : E →L[ℂ] E) (a : A) (x : E) :
    hilbertAmplification T (lp.single 2 a x) = lp.single 2 a (T x) := by
  apply lp.ext
  funext b
  change T ((lp.single 2 a x : ConstantHilbertSum A E) b) = (lp.single 2 a (T x) : ConstantHilbertSum A E) b
  simp only [lp.single_apply, Pi.single_apply]
  split_ifs <;> simp

/-- A nonempty amplification index gives a genuine faithful embedding of all bounded operators. -/
theorem hilbertAmplificationHom_injective [Nonempty A] :
    Function.Injective (hilbertAmplificationHom (A := A) (E := E)) := by
  intro T S h
  obtain ⟨a⟩ := ‹Nonempty A›
  apply ContinuousLinearMap.ext
  intro x
  have hx := congrArg (fun F : ConstantHilbertSum A E →L[ℂ] ConstantHilbertSum A E =>
    F (lp.single 2 a x) a) h
  change hilbertAmplification T (lp.single 2 a x) a = hilbertAmplification S (lp.single 2 a x) a at hx
  rw [hilbertAmplification_single, hilbertAmplification_single] at hx
  simpa only [lp.single_apply, Pi.single_eq_same] using hx

variable {I J : Type*}

/-- Each complete prefix sector genuinely intertwines the included creation operators. -/
theorem prefixTailEmbedding_creation_comp (t : PrefixTail I J) (i : I) :
    (prefixTailEmbedding t).toContinuousLinearMap.comp (creation i) =
      (creation (Sum.inl i)).comp (prefixTailEmbedding t).toContinuousLinearMap := by
  apply lp.ext_continuousLinearMap (ENNReal.ofNat_ne_top (n := 2))
  intro w
  apply ContinuousLinearMap.ext
  intro c
  change prefixTailEmbedding t (creation i (lp.single 2 w c)) =
    creation (Sum.inl i) (prefixTailEmbedding t (lp.single 2 w c))
  have hw : lp.single 2 w c = c • word w := by
    apply lp.ext
    funext v
    simp [word, lp.single_apply, Pi.single_apply]
  have he (v : List I) : prefixTailEmbedding t (word v) = word (joinPrefixTail (v, t)) := by
    have h1 : word v = lp.single 2 v (1 : ℂ) := by
      apply lp.ext
      funext u
      simp [word, lp.single_apply, Pi.single_apply]
    rw [h1, prefixTailEmbedding_single, one_smul]
  rw [hw, map_smul, creation_word, map_smul, he]
  rw [map_smul, he, map_smul, creation_word]
  rfl

/-- True unital embedding of every bounded prefix operator on the whole doubled word space. -/
def prefixOperatorEmbedding : (WordSpace I →L[ℂ] WordSpace I) →⋆ₐ[ℂ]
    (WordSpace (Sum I J) →L[ℂ] WordSpace (Sum I J)) :=
  prefixTailDecomposition.symm.conjStarAlgEquiv.toStarAlgHom.comp hilbertAmplificationHom

theorem prefixOperatorEmbedding_injective :
    Function.Injective (prefixOperatorEmbedding (I := I) (J := J)) :=
  prefixTailDecomposition.symm.conjStarAlgEquiv.injective.comp hilbertAmplificationHom_injective

/-- The embedding acts by the original operator in EVERY complete prefix sector. -/
theorem prefixOperatorEmbedding_sector (T : WordSpace I →L[ℂ] WordSpace I)
    (t : PrefixTail I J) (f : WordSpace I) :
    prefixOperatorEmbedding T (prefixTailEmbedding t f) = prefixTailEmbedding t (T f) := by
  rw [← prefixTailDecomposition_symm_single, ← prefixTailDecomposition_symm_single]
  change prefixTailDecomposition.symm (hilbertAmplification T
    (prefixTailDecomposition (prefixTailDecomposition.symm (lp.single 2 t f)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact congrArg prefixTailDecomposition.symm (hilbertAmplification_single T t f)

/-- Actual generator identification on the whole completed word Fock space. -/
theorem prefixOperatorEmbedding_creation (i : I) :
    prefixOperatorEmbedding (J := J) (creation i) = creation (Sum.inl i) := by
  apply prefixTailDecomposition.conjStarAlgEquiv.injective
  apply lp.ext_continuousLinearMap (ENNReal.ofNat_ne_top (n := 2))
  intro t
  apply ContinuousLinearMap.ext
  intro f
  apply prefixTailDecomposition.symm.injective
  change prefixTailDecomposition.symm
    (prefixTailDecomposition (prefixOperatorEmbedding (creation i)
      (prefixTailDecomposition.symm (lp.single 2 t f)))) =
    prefixTailDecomposition.symm
      (prefixTailDecomposition (creation (Sum.inl i)
        (prefixTailDecomposition.symm (lp.single 2 t f))))
  rw [LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.symm_apply_apply]
  rw [prefixTailDecomposition_symm_single, prefixOperatorEmbedding_sector]
  exact DFunLike.congr_fun (prefixTailEmbedding_creation_comp t i) f

/-- The actual Hilbert adjoint is transported to the included annihilator. -/
theorem prefixOperatorEmbedding_annihilation (i : I) :
    prefixOperatorEmbedding (J := J) (annihilation i) = annihilation (Sum.inl i) := by
  change prefixOperatorEmbedding (star (creation i)) = star (creation (Sum.inl i))
  rw [map_star, prefixOperatorEmbedding_creation]

/-- Exact real-field generator identification, rather than an abstract isomorphic copy. -/
theorem prefixOperatorEmbedding_semicircular (i : I) :
    prefixOperatorEmbedding (J := J) (semicircular i) = semicircular (Sum.inl i) := by
  rw [semicircular, map_add, prefixOperatorEmbedding_creation, prefixOperatorEmbedding_annihilation]
  rfl

end FreeProbability.Fock

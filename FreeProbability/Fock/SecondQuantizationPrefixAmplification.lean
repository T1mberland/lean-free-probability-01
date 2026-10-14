import FreeProbability.Fock.SecondQuantizationPrefixHilbert

/-! # Actual bounded amplification on an arbitrary complete Hilbert sum -/
noncomputable section
open scoped Classical InnerProductSpace ENNReal
namespace FreeProbability.Fock
variable {A E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

abbrev ConstantHilbertSum (A E : Type*) [NormedAddCommGroup E] := lp (fun _ : A => E) 2

/-- Apply the same actual bounded operator in every coordinate, including infinite amplitudes. -/
def hilbertAmplificationLinear (T : E →L[ℂ] E) :
    ConstantHilbertSum A E →ₗ[ℂ] ConstantHilbertSum A E where
  toFun f := ⟨fun a => T (f a), (lp.memℓp ((‖T‖ : ℂ) • f)).mono' (by
    intro a
    change ‖T (f a)‖ ≤ ‖(‖T‖ : ℂ) • f a‖
    simpa [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg T)]
      using T.le_opNorm (f a))⟩
  map_add' f g := by apply lp.ext; funext a; exact map_add T (f a) (g a)
  map_smul' c f := by apply lp.ext; funext a; exact map_smul T c (f a)

omit [CompleteSpace E] in
theorem norm_hilbertAmplificationLinear_le (T : E →L[ℂ] E) (f : ConstantHilbertSum A E) :
    ‖hilbertAmplificationLinear T f‖ ≤ ‖T‖ * ‖f‖ := by
  have hh : ‖hilbertAmplificationLinear T f‖ ≤ ‖(‖T‖ : ℂ) • f‖ := by
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro a
    change ‖T (f a)‖ ≤ ‖(‖T‖ : ℂ) • f a‖
    simpa [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg T)]
      using T.le_opNorm (f a)
  calc
    _ ≤ ‖(‖T‖ : ℂ) • f‖ := hh
    _ = ‖(‖T‖ : ℂ)‖ * ‖f‖ := norm_smul _ _
    _ = _ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg T)]

/-- Genuine bounded operator amplification on the complete external Hilbert sum. -/
def hilbertAmplification (T : E →L[ℂ] E) : ConstantHilbertSum A E →L[ℂ] ConstantHilbertSum A E :=
  (hilbertAmplificationLinear T).mkContinuous ‖T‖ (norm_hilbertAmplificationLinear_le T)

omit [CompleteSpace E] in
@[simp] theorem hilbertAmplification_apply (T : E →L[ℂ] E) (f : ConstantHilbertSum A E) (a : A) :
    hilbertAmplification T f a = T (f a) := rfl

theorem hilbertAmplification_adjoint (T : E →L[ℂ] E) :
    hilbertAmplification (A := A) T.adjoint = (hilbertAmplification T).adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f g
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro a
  exact T.adjoint_inner_left (g a) (f a)

/-- Genuine unital star homomorphism on ALL source bounded operators. -/
def hilbertAmplificationHom : (E →L[ℂ] E) →⋆ₐ[ℂ]
    (ConstantHilbertSum A E →L[ℂ] ConstantHilbertSum A E) where
  toFun := hilbertAmplification
  map_one' := by apply ContinuousLinearMap.ext; intro f; apply lp.ext; funext a; rfl
  map_mul' T S := by apply ContinuousLinearMap.ext; intro f; apply lp.ext; funext a; rfl
  map_zero' := by apply ContinuousLinearMap.ext; intro f; apply lp.ext; funext a; rfl
  map_add' T S := by apply ContinuousLinearMap.ext; intro f; apply lp.ext; funext a; rfl
  commutes' c := by apply ContinuousLinearMap.ext; intro f; apply lp.ext; funext a; rfl
  map_star' T := hilbertAmplification_adjoint T

omit [CompleteSpace E] in
theorem norm_hilbertAmplification_le (T : E →L[ℂ] E) :
    ‖hilbertAmplification (A := A) T‖ ≤ ‖T‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) (norm_hilbertAmplificationLinear_le T)

end FreeProbability.Fock

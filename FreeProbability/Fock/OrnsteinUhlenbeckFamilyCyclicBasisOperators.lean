import FreeProbability.Fock.OrnsteinUhlenbeckFamilyCyclicBasisOperatorsAdapted

/-! Actual prescribed-family word operator representation and right-field commutation.
No surjectivity onto a full word von Neumann algebra is assumed. -/
noncomputable section
open scoped Classical InnerProductSpace
namespace FreeProbability.Fock
variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Actual whole-double-commutant cyclic representation, transported to original-index completed words. -/
def familyWordRepresentation (e : I → H) (he : Orthonormal ℂ e) :
    tensorFamilyDoubleAlgebra e →⋆ₐ[ℂ] (WordSpace I →L[ℂ] WordSpace I) :=
  (familyCyclicWordUnitary e he).symm.conjStarAlgEquiv.toStarAlgHom.comp (ouVonNeumannCyclicAction e)

/-- Exact intertwining with the actual full adapted operator, on every completed original word vector. -/
theorem familyWordRepresentation_adapted {e : I → H} (d : OrthonormalFamilyExtension e)
    (he : Orthonormal ℂ e) (T : tensorFamilyDoubleAlgebra e) (f : WordSpace I) :
    d.tensorOperatorTransport.symm (T : TensorFullFock H →L[ℂ] TensorFullFock H)
      (familyCyclicAdaptedIsometry d he f) =
        familyCyclicAdaptedIsometry d he (familyWordRepresentation e he T f) := by
  change d.tensorTransport.symm
      ((T : TensorFullFock H →L[ℂ] TensorFullFock H)
        (d.tensorTransport (familyCyclicAdaptedIsometry d he f))) =
    d.tensorTransport.symm
      (familyCyclicWordUnitary e he
        ((familyCyclicWordUnitary e he).symm
          (ouVonNeumannCyclicAction e T (familyCyclicWordUnitary e he f))) : TensorFullFock H)
  rw [familyCyclicAdaptedIsometry_tensor, LinearIsometryEquiv.apply_symm_apply]
  rfl

 theorem familyCyclicAdaptedIsometry_right {e : I → H} (d : OrthonormalFamilyExtension e)
    (he : Orthonormal ℂ e) (i : I) (f : WordSpace I) :
    familyCyclicAdaptedIsometry d he (rightSemicircular i f) =
      rightSemicircular (d.index i) (familyCyclicAdaptedIsometry d he f) :=
  DFunLike.congr_fun (familyCyclicAdaptedIsometry_right_comp d he i) f

/-- The actual represented original given left field is exactly its canonical word field. -/
theorem familyWordRepresentation_field (e : I → H) (he : Orthonormal ℂ e) (i : I) :
    familyWordRepresentation e he (ouCyclicNativeInclusion e (ouCyclicNativeField e i)) = semicircular i := by
  let d := orthonormalFamilyExtension he
  have ha : d.tensorOperatorTransport.symm
      (ouCyclicNativeInclusion e (ouCyclicNativeField e i) : TensorFullFock H →L[ℂ] TensorFullFock H) =
      semicircular (d.index i) := by
    apply d.tensorOperatorTransport.injective
    change d.tensorOperatorTransport (d.tensorOperatorTransport.symm
        (ouCyclicNativeInclusion e (ouCyclicNativeField e i) : TensorFullFock H →L[ℂ] TensorFullFock H)) =
      d.tensorOperatorTransport (semicircular (d.index i))
    rw [StarAlgEquiv.apply_symm_apply]
    change tensorFamilyField e i = d.tensorOperatorTransport (semicircular (d.index i))
    rw [← d.field_eq_semicircular, d.tensorOperatorTransport_field]
    rfl
  apply ContinuousLinearMap.ext
  intro f
  apply (familyCyclicAdaptedIsometry d he).injective
  rw [← familyWordRepresentation_adapted, ha]
  exact (DFunLike.congr_fun (familyCyclicAdaptedIsometry_left_comp d he i) f).symm

/-- EVERY actual represented whole-algebra operator commutes with ALL original-index right fields. -/
theorem familyWordRepresentation_commute_right (e : I → H) (he : Orthonormal ℂ e)
    (T : tensorFamilyDoubleAlgebra e) (i : I) :
    Commute (familyWordRepresentation e he T) (rightSemicircular i) := by
  let d := orthonormalFamilyExtension he
  have ha : Commute (d.tensorOperatorTransport.symm (T : TensorFullFock H →L[ℂ] TensorFullFock H))
      (rightSemicircular (d.index i)) :=
    wordSemicircularVonNeumannAlgebra_commute_right
      (d.tensorFamilyVonNeumann_maps_into_fullWord T.property) (d.index i)
  apply ContinuousLinearMap.ext
  intro f
  apply (familyCyclicAdaptedIsometry d he).injective
  change familyCyclicAdaptedIsometry d he
      (familyWordRepresentation e he T (rightSemicircular i f)) =
    familyCyclicAdaptedIsometry d he (rightSemicircular i (familyWordRepresentation e he T f))
  rw [← familyWordRepresentation_adapted, familyCyclicAdaptedIsometry_right,
    familyCyclicAdaptedIsometry_right, ← familyWordRepresentation_adapted]
  exact DFunLike.congr_fun ha.eq (familyCyclicAdaptedIsometry d he f)

/-- Genuine full-tensor right field selected from the actual complete adapted basis. -/
def familyTensorRightField {e : I → H} (d : OrthonormalFamilyExtension e) (i : I) :
    TensorFullFock H →L[ℂ] TensorFullFock H := d.tensorOperatorTransport (rightSemicircular (d.index i))

/-- Its restriction to the ORIGINAL cyclic space agrees exactly with the original canonical right field. -/
theorem familyTensorRightField_cyclic {e : I → H} (d : OrthonormalFamilyExtension e)
    (he : Orthonormal ℂ e) (i : I) (f : familyCyclicSpace e) :
    familyTensorRightField d i (f : TensorFullFock H) =
      (familyCyclicWordUnitary e he
        (rightSemicircular i ((familyCyclicWordUnitary e he).symm f)) : TensorFullFock H) := by
  have heq : d.tensorTransport.symm (f : TensorFullFock H) =
      familyCyclicAdaptedIsometry d he ((familyCyclicWordUnitary e he).symm f) := by
    change d.tensorTransport.symm (f : TensorFullFock H) =
      d.tensorTransport.symm
        (familyCyclicWordUnitary e he ((familyCyclicWordUnitary e he).symm f) : TensorFullFock H)
    rw [LinearIsometryEquiv.apply_symm_apply]
  change d.tensorTransport (rightSemicircular (d.index i) (d.tensorTransport.symm (f : TensorFullFock H))) = _
  rw [heq, ← familyCyclicAdaptedIsometry_right, familyCyclicAdaptedIsometry_tensor]

 theorem familyTensorRightField_mem_cyclic {e : I → H} (d : OrthonormalFamilyExtension e)
    (he : Orthonormal ℂ e) (i : I) {f : TensorFullFock H} (hf : f ∈ familyCyclicSpace e) :
    familyTensorRightField d i f ∈ familyCyclicSpace e := by
  rw [familyTensorRightField_cyclic d he i ⟨f, hf⟩]
  exact Subtype.property _

/-- Actual full-tensor right fields commute with every operator in the given whole double commutant. -/
theorem familyTensorRightField_commute {e : I → H} (d : OrthonormalFamilyExtension e)
    (T : tensorFamilyDoubleAlgebra e) (i : I) :
    Commute (T : TensorFullFock H →L[ℂ] TensorFullFock H) (familyTensorRightField d i) := by
  have ha := wordSemicircularVonNeumannAlgebra_commute_right
    (d.tensorFamilyVonNeumann_maps_into_fullWord T.property) (d.index i)
  have hm := congrArg d.tensorOperatorTransport ha.eq
  rw [map_mul, map_mul, StarAlgEquiv.apply_symm_apply] at hm
  exact hm

/-- Actual represented vacuum equals the genuine whole-algebra original-word coefficient vector. -/
theorem familyWordRepresentation_vacuum (e : I → H) (he : Orthonormal ℂ e)
    (T : tensorFamilyDoubleAlgebra e) :
    familyWordRepresentation e he T vacuum = familyVonNeumannWordCoefficients e he T := by
  change (familyCyclicWordUnitary e he).symm
    (ouVonNeumannCyclicAction e T (familyCyclicWordUnitary e he vacuum)) = _
  rw [familyCyclicWordUnitary_vacuum]
  rfl

theorem familyWordRepresentation_injective (e : I → H) (he : Orthonormal ℂ e) :
    Function.Injective (familyWordRepresentation e he) := by
  intro T S h
  apply ouVonNeumannCyclicAction_injective e he
  exact (familyCyclicWordUnitary e he).symm.conjStarAlgEquiv.injective h

 theorem familyWordRepresentation_norm (e : I → H) (he : Orthonormal ℂ e)
    (T : tensorFamilyDoubleAlgebra e) : ‖familyWordRepresentation e he T‖ = ‖T‖ :=
  NonUnitalStarAlgHom.norm_map _ (familyWordRepresentation_injective e he) T

/-- Actual represented family Wick operators equal the original-index canonical Wick operators. -/
theorem familyWordRepresentation_Wick (e : I → H) (he : Orthonormal ℂ e) (w : List I) :
    familyWordRepresentation e he (ouCyclicNativeInclusion e (familyClosedWick e w)) = wick w := by
  apply sub_eq_zero.mp
  apply eq_zero_of_commute_right_of_vacuum_eq_zero
  · intro i
    exact Commute.sub_left (familyWordRepresentation_commute_right e he _ i)
      (commute_right_of_mem_semicircularAlgebra (wick_mem_algebra w) i)
  · rw [sub_apply, familyWordRepresentation_vacuum, familyVonNeumannWordCoefficients_Wick,
      wick_vacuum, sub_self]

end FreeProbability.Fock

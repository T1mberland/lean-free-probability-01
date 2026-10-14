import FreeProbability.Fock.OrnsteinUhlenbeckSemigroupRange

/-! # Genuine unital completely positive OU self-maps on native generated C-star algebras -/
noncomputable section
open scoped Classical CStarAlgebra
namespace FreeProbability.Fock
variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The canonical C-star positive order on the native prescribed-family closure. -/
instance tensorFamilyAlgebraOrder (e : I → H) : PartialOrder (tensorFamilyAlgebra e) :=
  CStarAlgebra.spectralOrder _

instance tensorFamilyAlgebraStarOrderedRing (e : I → H) : StarOrderedRing (tensorFamilyAlgebra e) :=
  CStarAlgebra.spectralOrderedRing _

/-- Canonical matrix positivity is reflected by the actual inclusion into the ambient operator algebra. -/
theorem tensorFamilyMatrix_nonneg_of_coe {N : Type*} [Fintype N] (e : I → H)
    (M : CStarMatrix N N (tensorFamilyAlgebra e))
    (hM : 0 ≤ M.map (tensorFamilyAlgebra e).val) : 0 ≤ M := by
  let F : CStarMatrix N N (tensorFamilyAlgebra e) →⋆ₙₐ[ℂ]
      CStarMatrix N N (TensorFullFock H →L[ℂ] TensorFullFock H) :=
    CStarMatrix.mapₙₐ (tensorFamilyAlgebra e).subtype.toNonUnitalStarAlgHom
  have hF : Function.Injective F := by
    intro A B h
    apply CStarMatrix.ext
    intro i j
    apply Subtype.ext
    exact congrArg (fun X : CStarMatrix N N (TensorFullFock H →L[ℂ] TensorFullFock H) => X i j) h
  have hh : F 0 ≤ F M := by
    rw [map_zero]
    exact hM
  exact (NonUnitalStarAlgHom.map_le_map_iff F hF).mp hh

/-- True complete positivity of the rotated dilation restricted to both literal generated closures. -/
def rotatedIncludedFamilyCP (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1) (e : I → H) :
    tensorFamilyAlgebra (fun i => doubledFirst H (e i)) →CP tensorFamilyAlgebra e where
  toLinearMap := rotatedIncludedFamilyMap r s hrs e
  map_cstarMatrix_nonneg' _k M hM := by
    apply tensorFamilyMatrix_nonneg_of_coe e
    have hi : 0 ≤ M.map (tensorFamilyAlgebra (fun i => doubledFirst H (e i))).val :=
      map_nonneg (CStarMatrix.mapₙₐ (tensorFamilyAlgebra (fun i => doubledFirst H (e i))).subtype.toNonUnitalStarAlgHom) hM
    have hp := (rotatedFockCompression H r s hrs).map_cstarMatrix_nonneg
      (M.map (tensorFamilyAlgebra (fun i => doubledFirst H (e i))).val) hi
    exact hp

/-- Actual OU rotation-compression self-map on the native algebra of any orthonormal family. -/
def familyOU (e : I → H) (he : Orthonormal ℂ e) (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1) :
    tensorFamilyAlgebra e →CP tensorFamilyAlgebra e where
  toLinearMap := (rotatedIncludedFamilyCP r s hrs e).toLinearMap.comp
    (includedFamilyEmbedding (doubledFirst H) e he).toAlgHom.toLinearMap
  map_cstarMatrix_nonneg' _k M hM := by
    let F := includedFamilyEmbedding (doubledFirst H) e he
    have hi : 0 ≤ M.map F := map_nonneg (CStarMatrix.mapₙₐ F.toNonUnitalStarAlgHom) hM
    exact (rotatedIncludedFamilyCP r s hrs e).map_cstarMatrix_nonneg (M.map F) hi

@[simp] theorem familyOU_one (e : I → H) (he : Orthonormal ℂ e)
    (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1) : familyOU e he r s hrs 1 = 1 := by
  change rotatedIncludedFamilyMap r s hrs e (includedFamilyEmbedding (doubledFirst H) e he 1) = _
  rw [map_one, rotatedIncludedFamilyMap_one]

/-- Genuine operator norm contraction on the entire native C-star algebra. -/
theorem norm_familyOU_le (e : I → H) (he : Orthonormal ℂ e)
    (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1) (T : tensorFamilyAlgebra e) :
    ‖familyOU e he r s hrs T‖ ≤ ‖T‖ := by
  change ‖rotatedIncludedFamilyMap r s hrs e (includedFamilyEmbedding (doubledFirst H) e he T)‖ ≤ _
  exact (norm_rotatedIncludedFamilyMap_le _ _ _ _ _).trans (includedFamilyEmbedding_norm _ _ _ T).le

/-- The actual faithful tracial vacuum state is preserved by the OU self-map. -/
theorem familyOU_expectation (e : I → H) (he : Orthonormal ℂ e)
    (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1) (T : tensorFamilyAlgebra e) :
    (tensorFamilyVacuumState e).expectation (familyOU e he r s hrs T) =
      (tensorFamilyVacuumState e).expectation T := by
  change (tensorFamilyVacuumState e).expectation
    (rotatedIncludedFamilyMap r s hrs e (includedFamilyEmbedding (doubledFirst H) e he T)) = _
  rw [rotatedIncludedFamilyMap_expectation]
  have ht := includedFamilyCompression_expectation (doubledFirst H) e
    (includedFamilyEmbedding (doubledFirst H) e he T)
  have hi : includedFamilyCompression (doubledFirst H) e
      (includedFamilyEmbedding (doubledFirst H) e he T) = T :=
    (includedFamilyEquiv (doubledFirst H) e he).apply_symm_apply T
  rw [hi] at ht
  exact ht.symm

/-- Actual unital CP OU self-map at every nonnegative time. -/
def familyOUTime (e : I → H) (he : Orthonormal ℂ e) (t : ℝ) (ht : 0 ≤ t) :
    tensorFamilyAlgebra e →CP tensorFamilyAlgebra e :=
  familyOU e he (ouCosine t) (ouSine t) (ouRotation_parameters t ht)

end FreeProbability.Fock

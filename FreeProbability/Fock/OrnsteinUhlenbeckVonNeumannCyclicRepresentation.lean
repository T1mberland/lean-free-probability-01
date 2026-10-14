import FreeProbability.Fock.OrnsteinUhlenbeckVonNeumannCyclicVector

/-! Actual star representation of the entire prescribed double commutant on its original cyclic space. -/
noncomputable section
open scoped Classical InnerProductSpace
namespace FreeProbability.Fock
variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The original cyclic projection commutes with every actual double-commutant operator. -/
theorem ouVonNeumann_commute_cyclicProjection (e : I → H) (T : tensorFamilyDoubleAlgebra e) :
    Commute (ouFamilyCyclicProjection e) (T : TensorFullFock H →L[ℂ] TensorFullFock H) := by
  have hT : (T : TensorFullFock H →L[ℂ] TensorFullFock H) ∈
      Set.centralizer (Set.centralizer (Set.range (tensorFamilyField e))) := by
    rw [← tensorFamilyDoubleAlgebra_coe]
    exact T.property
  exact (Set.mem_centralizer_iff.mp hT) _ (ouFamilyCyclicProjection_mem_commutant e)

/-- EVERY whole-double-commutant operator preserves the ORIGINAL complete cyclic Hilbert space. -/
theorem ouVonNeumann_mem_cyclic (e : I → H) (T : tensorFamilyDoubleAlgebra e)
    {f : TensorFullFock H} (hf : f ∈ familyCyclicSpace e) :
    (T : TensorFullFock H →L[ℂ] TensorFullFock H) f ∈ familyCyclicSpace e := by
  apply (familyCyclicSpace e).starProjection_eq_self_iff.mp
  change ouFamilyCyclicProjection e ((T : TensorFullFock H →L[ℂ] TensorFullFock H) f) = _
  have he := DFunLike.congr_fun (ouVonNeumann_commute_cyclicProjection e T).eq f
  have hp : ouFamilyCyclicProjection e f = f := (familyCyclicSpace e).starProjection_eq_self_iff.mpr hf
  simpa only [mul_apply_eq_comp, hp] using he

/-- Actual restriction to the proved invariant cyclic Hilbert space, as a linear operator-valued map. -/
def ouVonNeumannCyclicActionLinear (e : I → H) :
    tensorFamilyDoubleAlgebra e →ₗ[ℂ] (familyCyclicSpace e →L[ℂ] familyCyclicSpace e) where
  toFun T := (T : TensorFullFock H →L[ℂ] TensorFullFock H).restrict (fun _ hf => ouVonNeumann_mem_cyclic e T hf)
  map_add' T S := by
    apply ContinuousLinearMap.ext
    intro f
    apply Subtype.ext
    rfl
  map_smul' c T := by
    apply ContinuousLinearMap.ext
    intro f
    apply Subtype.ext
    rfl

/-- Genuine unital star representation on the SAME original complete cyclic Hilbert space. -/
def ouVonNeumannCyclicAction (e : I → H) :
    tensorFamilyDoubleAlgebra e →⋆ₐ[ℂ] (familyCyclicSpace e →L[ℂ] familyCyclicSpace e) where
  toAlgHom := AlgHom.ofLinearMap (ouVonNeumannCyclicActionLinear e)
    (by apply ContinuousLinearMap.ext; intro f; apply Subtype.ext; rfl)
    (by intro T S; apply ContinuousLinearMap.ext; intro f; apply Subtype.ext; rfl)
  map_star' T := by
    change ouVonNeumannCyclicActionLinear e (star T) = (ouVonNeumannCyclicActionLinear e T).adjoint
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    intro f g
    change inner ℂ ((T : TensorFullFock H →L[ℂ] TensorFullFock H).adjoint (f : TensorFullFock H))
      (g : TensorFullFock H) =
      inner ℂ (f : TensorFullFock H) ((T : TensorFullFock H →L[ℂ] TensorFullFock H) (g : TensorFullFock H))
    exact (T : TensorFullFock H →L[ℂ] TensorFullFock H).adjoint_inner_left _ _

/-- The actual cyclic action implements whole-algebra left multiplication on every vacuum vector. -/
theorem ouVonNeumannCyclicAction_vector (e : I → H) (T S : tensorFamilyDoubleAlgebra e) :
    ouVonNeumannCyclicAction e T (ouVonNeumannCyclicVector e S) = ouVonNeumannCyclicVector e (T * S) := by
  apply Subtype.ext
  rfl

/-- Actual ON vacuum separation makes the complete cyclic representation faithful. -/
theorem ouVonNeumannCyclicAction_injective (e : I → H) (he : Orthonormal ℂ e) :
    Function.Injective (ouVonNeumannCyclicAction e) := by
  intro T S h
  apply ouVonNeumann_vacuum_ext e he
  have hv := congrArg (fun A : familyCyclicSpace e →L[ℂ] familyCyclicSpace e =>
    (A (familyCyclicVacuum e) : TensorFullFock H)) h
  exact hv

/-- The genuine cyclic star representation preserves the full operator norm for an ON family. -/
theorem ouVonNeumannCyclicAction_norm (e : I → H) (he : Orthonormal ℂ e)
    (T : tensorFamilyDoubleAlgebra e) : ‖ouVonNeumannCyclicAction e T‖ = ‖T‖ :=
  NonUnitalStarAlgHom.norm_map _ (ouVonNeumannCyclicAction_injective e he) T

end FreeProbability.Fock

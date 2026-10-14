import FreeProbability.Fock.OrnsteinUhlenbeckDilationIntertwining
import FreeProbability.Fock.TensorFamilyFaithfulnessEquiv

/-! # The included field algebra genuinely reduces the included full Fock space -/
noncomputable section
open scoped Classical InnerProductSpace
namespace FreeProbability.Fock
variable {I H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Actual orthogonal projection onto the second-quantized isometry's range. -/
def fockInclusionProjection (V : H →ₗᵢ[ℂ] K) : TensorFullFock K →L[ℂ] TensorFullFock K :=
  (secondQuantizationIsometry V).toContinuousLinearMap.comp
    (secondQuantizationIsometry V).toContinuousLinearMap.adjoint

@[simp] theorem fockInclusionProjection_star (V : H →ₗᵢ[ℂ] K) :
    star (fockInclusionProjection V) = fockInclusionProjection V := by
  change ((secondQuantizationIsometry V).toContinuousLinearMap.comp
    (secondQuantizationIsometry V).toContinuousLinearMap.adjoint).adjoint = _
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
  rfl

/-- Actual included fields intertwine on the entire complete Fock space. -/
theorem tensorFamilyField_inclusion_comp (V : H →ₗᵢ[ℂ] K) (e : I → H) (i : I) :
    (tensorFamilyField (fun j => V (e j)) i).comp (secondQuantizationIsometry V).toContinuousLinearMap =
      (secondQuantizationIsometry V).toContinuousLinearMap.comp (tensorFamilyField e i) := by
  apply ContinuousLinearMap.ext
  intro f
  have hc := DFunLike.congr_fun (secondQuantizationIsometry_creation_comp V (e i)) f
  have ha := DFunLike.congr_fun (inclusion_annihilation_comp V (e i)) f
  change tensorCreation K (V (e i)) (secondQuantizationIsometry V f) +
    tensorAnnihilation K (V (e i)) (secondQuantizationIsometry V f) =
      secondQuantizationIsometry V (tensorCreation H (e i) f + tensorAnnihilation H (e i) f)
  rw [map_add]
  exact congrArg₂ (· + ·) hc.symm ha

/-- Actual fields are self-adjoint, on both the original and included Hilbert spaces. -/
theorem ou_tensorFamilyField_adjoint (e : I → H) (i : I) :
    (tensorFamilyField e i).adjoint = tensorFamilyField e i := by
  change (tensorCreation H (e i) + (tensorCreation H (e i)).adjoint).adjoint = _
  rw [map_add, ContinuousLinearMap.adjoint_adjoint]
  exact add_comm _ _

/-- Included generators commute with the actual range projection. -/
theorem tensorFamilyField_commutes_inclusionProjection (V : H →ₗᵢ[ℂ] K) (e : I → H) (i : I) :
    tensorFamilyField (fun j => V (e j)) i * fockInclusionProjection V =
      fockInclusionProjection V * tensorFamilyField (fun j => V (e j)) i := by
  let W := (secondQuantizationIsometry V).toContinuousLinearMap
  let T := tensorFamilyField (fun j => V (e j)) i
  let S := tensorFamilyField e i
  have ht : T.comp W = W.comp S := tensorFamilyField_inclusion_comp V e i
  have ha := congrArg ContinuousLinearMap.adjoint ht
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp] at ha
  change W.adjoint.comp T.adjoint = S.adjoint.comp W.adjoint at ha
  rw [ou_tensorFamilyField_adjoint, ou_tensorFamilyField_adjoint] at ha
  change T.comp (W.comp W.adjoint) = (W.comp W.adjoint).comp T
  rw [← ContinuousLinearMap.comp_assoc, ht, ContinuousLinearMap.comp_assoc, ← ha,
    ← ContinuousLinearMap.comp_assoc]

/-- The full literal norm closure commutes with the range projection, without assuming multiplicativity. -/
theorem tensorFamilyAlgebra_commutes_inclusionProjection (V : H →ₗᵢ[ℂ] K) (e : I → H)
    {T : TensorFullFock K →L[ℂ] TensorFullFock K}
    (hT : T ∈ tensorFamilyAlgebra (fun i => V (e i))) :
    fockInclusionProjection V * T = T * fockInclusionProjection V := by
  let B := StarSubalgebra.centralizer ℂ ({fockInclusionProjection V} : Set _)
  have hp : StarAlgebra.adjoin ℂ (Set.range (tensorFamilyField (fun i => V (e i)))) ≤ B := by
    apply StarAlgebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
    intro P hP
    have he : P = fockInclusionProjection V := Set.mem_singleton_iff.mp hP
    subst P
    rw [fockInclusionProjection_star]
    exact ⟨(tensorFamilyField_commutes_inclusionProjection V e i).symm,
      (tensorFamilyField_commutes_inclusionProjection V e i).symm⟩
  have hc : IsClosed (B : Set (TensorFullFock K →L[ℂ] TensorFullFock K)) := by
    change IsClosed (({fockInclusionProjection V} ∪ star {fockInclusionProjection V} : Set _).centralizer)
    exact Set.isClosed_centralizer _
  have hb := StarSubalgebra.topologicalClosure_minimal hp hc hT
  exact (((StarSubalgebra.mem_centralizer_iff ℂ).mp hb) _ (Set.mem_singleton _)).1

/-- Every included closed-algebra operator intertwines with its actual compression. -/
theorem tensorFamilyAlgebra_inclusion_comp (V : H →ₗᵢ[ℂ] K) (e : I → H)
    {T : TensorFullFock K →L[ℂ] TensorFullFock K}
    (hT : T ∈ tensorFamilyAlgebra (fun i => V (e i))) :
    T.comp (secondQuantizationIsometry V).toContinuousLinearMap =
      (secondQuantizationIsometry V).toContinuousLinearMap.comp (secondQuantizationCompression V T) := by
  let W := (secondQuantizationIsometry V).toContinuousLinearMap
  have hp : (fockInclusionProjection V).comp W = W := by
    change (W.comp W.adjoint).comp W = W
    rw [ContinuousLinearMap.comp_assoc, secondQuantizationIsometry_adjoint_comp]
    rfl
  have ht := tensorFamilyAlgebra_commutes_inclusionProjection V e hT
  change (fockInclusionProjection V).comp T = T.comp (fockInclusionProjection V) at ht
  change T.comp W = W.comp (W.adjoint.comp (T.comp W))
  calc
    T.comp W = T.comp ((fockInclusionProjection V).comp W) := congrArg T.comp hp.symm
    _ = ((fockInclusionProjection V).comp T).comp W := by rw [← ContinuousLinearMap.comp_assoc, ← ht]
    _ = _ := by change ((W.comp W.adjoint).comp T).comp W = _; rw [ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc]

/-- Compression genuinely multiplies on the reducing included algebra only. -/
theorem tensorFamilyAlgebra_compression_mul (V : H →ₗᵢ[ℂ] K) (e : I → H)
    (T S : TensorFullFock K →L[ℂ] TensorFullFock K)
    (hS : S ∈ tensorFamilyAlgebra (fun i => V (e i))) :
    secondQuantizationCompression V (T * S) =
      secondQuantizationCompression V T * secondQuantizationCompression V S := by
  have hs := tensorFamilyAlgebra_inclusion_comp V e hS
  change (secondQuantizationIsometry V).toContinuousLinearMap.adjoint.comp
      ((T.comp S).comp (secondQuantizationIsometry V).toContinuousLinearMap) = _
  rw [ContinuousLinearMap.comp_assoc, hs]
  rfl

end FreeProbability.Fock

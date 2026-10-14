import FreeProbability.Fock.OrnsteinUhlenbeckL2Intertwining

/-!
# Actual cyclic Hilbert-space OU extension

The cyclic space is the complete closure of native-algebra vacuum vectors in
fixed tensor Fock space. No spanning assumption identifies it with full Fock.
-/
noncomputable section
open scoped Classical InnerProductSpace
namespace FreeProbability.Fock
variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual complete cyclic Hilbert subspace, retaining arbitrary nonspanning families. -/
def familyCyclicSpace (e : I → H) : Submodule ℂ (TensorFullFock H) :=
  (familyVacuumVector e).range.topologicalClosure

instance (e : I → H) : CompleteSpace (familyCyclicSpace e) := by
  unfold familyCyclicSpace
  infer_instance

instance (e : I → H) : IsClosed (familyCyclicSpace e : Set (TensorFullFock H)) :=
  (familyVacuumVector e).range.isClosed_topologicalClosure

/-- Each actual vacuum vector belongs to the genuine cyclic Hilbert closure. -/
theorem familyVacuumVector_mem_cyclic (e : I → H) (T : tensorFamilyAlgebra e) :
    familyVacuumVector e T ∈ familyCyclicSpace e :=
  (familyVacuumVector e).range.le_topologicalClosure ⟨T, rfl⟩

/-- Actual bounded vacuum evaluation, now with the complete cyclic Hilbert codomain. -/
def familyCyclicVector (e : I → H) : tensorFamilyAlgebra e →L[ℂ] familyCyclicSpace e :=
  (familyVacuumVector e).codRestrict (familyCyclicSpace e) (familyVacuumVector_mem_cyclic e)

/-- The native vacuum vectors are genuinely dense in the complete cyclic Hilbert space. -/
theorem familyCyclicVector_denseRange (e : I → H) : DenseRange (familyCyclicVector e) := by
  rw [DenseRange, Subtype.dense_iff, ← Set.range_comp]
  change (familyCyclicSpace e : Set (TensorFullFock H)) ⊆ closure (Set.range (familyVacuumVector e))
  exact Set.Subset.rfl

/-- Actual degree damping preserves the full complete cyclic closure, by OU vacuum implementation. -/
theorem degreeDamping_mem_cyclic (e : I → H) (he : Orthonormal ℂ e) (t : ℝ) (ht : 0 ≤ t)
    {f : TensorFullFock H} (hf : f ∈ familyCyclicSpace e) :
    degreeDamping H t ht f ∈ familyCyclicSpace e := by
  have hp : ((familyVacuumVector e).range : Set (TensorFullFock H)) ⊆ (degreeDamping H t ht) ⁻¹' (familyCyclicSpace e : Set _) := by
    intro f hf
    obtain ⟨T, rfl⟩ := hf
    change degreeDamping H t ht (familyVacuumVector e T) ∈ familyCyclicSpace e
    rw [← familyOUTime_vacuum_vector e he t ht T]
    exact familyVacuumVector_mem_cyclic e _
  have hc : IsClosed ((degreeDamping H t ht) ⁻¹' (familyCyclicSpace e : Set _)) :=
    (familyVacuumVector e).range.isClosed_topologicalClosure.preimage (degreeDamping H t ht).continuous
  change f ∈ closure ((familyVacuumVector e).range : Set (TensorFullFock H)) at hf
  exact closure_minimal hp hc hf

/-- Genuine bounded L² contraction on the complete cyclic Hilbert space. -/
def familyOUL2 (e : I → H) (he : Orthonormal ℂ e) (t : ℝ) (ht : 0 ≤ t) :
    familyCyclicSpace e →L[ℂ] familyCyclicSpace e :=
  (degreeDamping H t ht).restrict (fun _f hf => degreeDamping_mem_cyclic e he t ht hf)

/-- Actual cyclic L² extension agrees with the native OU map on all original vacuum vectors. -/
theorem familyOUL2_cyclicVector (e : I → H) (he : Orthonormal ℂ e) (t : ℝ) (ht : 0 ≤ t)
    (T : tensorFamilyAlgebra e) :
    familyOUL2 e he t ht (familyCyclicVector e T) = familyCyclicVector e (familyOUTime e he t ht T) :=
  Subtype.ext (familyOUTime_vacuum_vector e he t ht T).symm

theorem norm_familyOUL2_le (e : I → H) (he : Orthonormal ℂ e) (t : ℝ) (ht : 0 ≤ t)
    (f : familyCyclicSpace e) : ‖familyOUL2 e he t ht f‖ ≤ ‖f‖ := norm_degreeDamping_le H t ht f

/-- Zero-time identity on the entire actual complete cyclic Hilbert space. -/
@[simp] theorem familyOUL2_zero (e : I → H) (he : Orthonormal ℂ e) :
    familyOUL2 e he 0 (le_refl 0) = ContinuousLinearMap.id ℂ (familyCyclicSpace e) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  exact DFunLike.congr_fun (degreeDamping_zero H) (f : TensorFullFock H)

/-- Actual additive-time contraction semigroup on the complete cyclic Hilbert space. -/
theorem familyOUL2_add (e : I → H) (he : Orthonormal ℂ e) (t u : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    (familyOUL2 e he t ht).comp (familyOUL2 e he u hu) =
      familyOUL2 e he (t + u) (add_nonneg ht hu) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  exact DFunLike.congr_fun (degreeDamping_add H t u ht hu) (f : TensorFullFock H)

/-- The cyclic unit vacuum, as a genuine vector in the complete Hilbert representation. -/
def familyCyclicVacuum (e : I → H) : familyCyclicSpace e :=
  familyCyclicVector e 1

@[simp] theorem familyOUL2_vacuum (e : I → H) (he : Orthonormal ℂ e) (t : ℝ) (ht : 0 ≤ t) :
    familyOUL2 e he t ht (familyCyclicVacuum e) = familyCyclicVacuum e := by
  rw [familyCyclicVacuum, familyOUL2_cyclicVector, familyOUTime_one]

/-- The actual L² extension is uniquely determined by its dense native vacuum orbit. -/
theorem familyOUL2_unique (e : I → H) (he : Orthonormal ℂ e) (t : ℝ) (ht : 0 ≤ t)
    (F : familyCyclicSpace e →L[ℂ] familyCyclicSpace e)
    (hF : ∀ T : tensorFamilyAlgebra e,
      F (familyCyclicVector e T) = familyCyclicVector e (familyOUTime e he t ht T)) :
    F = familyOUL2 e he t ht := by
  apply DFunLike.ext'
  apply Continuous.ext_on (familyCyclicVector_denseRange e) F.continuous (familyOUL2 e he t ht).continuous
  rintro _ ⟨T, rfl⟩
  exact (hF T).trans (familyOUL2_cyclicVector e he t ht T).symm

end FreeProbability.Fock

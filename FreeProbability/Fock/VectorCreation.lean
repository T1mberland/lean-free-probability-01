import FreeProbability.Fock.CatalanMoments

/-!
# Creation and annihilation for arbitrary square-summable one-particle vectors

The word Fock model now admits creation by every vector of `ℓ²(I, ℂ)`, with
its exact norm and canonical inner-product relations. Basis identification with
completed tensor powers is a separate obligation.
-/

noncomputable section
open scoped Classical InnerProductSpace ENNReal

namespace FreeProbability.Fock

variable {I : Type*}

/-- The genuine completed one-particle Hilbert space of the word model. -/
abbrev OneParticleSpace (I : Type*) := lp (fun _ : I => ℂ) 2

/-- Distinct canonical creation ranges are orthogonal on the entire Hilbert space. -/
theorem orthogonal_creationFamily :
    OrthogonalFamily ℂ (fun _ : I => WordSpace I) (fun i => creationIsometry i) := by
  intro i j hij f g
  change inner ℂ (creation i f) (creation j g) = 0
  rw [← ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ f (annihilation i (creation j g)) = 0
  have h := congrArg (fun T : WordSpace I →L[ℂ] WordSpace I => T g) (annihilation_creation i j)
  simp only [hij, ite_false, ContinuousLinearMap.comp_apply, zero_apply] at h
  rw [h]
  simp

/-- Orthogonality combines all canonical creation ranges into one Hilbert-sum isometry. -/
def creationFamilyIsometry : lp (fun _ : I => WordSpace I) 2 →ₗᵢ[ℂ] WordSpace I :=
  orthogonal_creationFamily.linearIsometry

/-- The genuine Hilbert-summable elementary tensor with coordinates `h_i f`. -/
def tensorVector (h : OneParticleSpace I) (f : WordSpace I) : lp (fun _ : I => WordSpace I) 2 :=
  ⟨fun i => h i • f, by
    apply Memℓp.of_norm
    convert (lp.memℓp h).norm.const_smul ‖f‖ using 1
    ext i
    simp [norm_smul, mul_comm]⟩

@[simp] theorem tensorVector_apply (h : OneParticleSpace I) (f : WordSpace I) (i : I) :
    tensorVector h f i = h i • f := rfl

/-- Inner products of elementary Hilbert tensors factor without any finiteness assumption. -/
theorem inner_tensorVector (h k : OneParticleSpace I) (f g : WordSpace I) :
    inner ℂ (tensorVector h f) (tensorVector k g) = inner ℂ h k * inner ℂ f g := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  simp only [tensorVector_apply, inner_smul_left, inner_smul_right]
  simp_rw [← mul_assoc]
  rw [← tsum_mul_right]
  congr 1

/-- Exact norm of an elementary Hilbert tensor. -/
theorem norm_tensorVector (h : OneParticleSpace I) (f : WordSpace I) :
    ‖tensorVector h f‖ = ‖h‖ * ‖f‖ := by
  have ht := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (tensorVector h f)
  have hh := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) h
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, tensorVector_apply, norm_smul, mul_pow] at ht hh
  rw [tsum_mul_right, ← hh] at ht
  nlinarith [norm_nonneg (tensorVector h f), norm_nonneg h, norm_nonneg f,
    mul_nonneg (norm_nonneg h) (norm_nonneg f)]

/-- Creation by `h` as a linear map on Fock space. -/
def vectorCreationLinear (h : OneParticleSpace I) : WordSpace I →ₗ[ℂ] WordSpace I where
  toFun f := creationFamilyIsometry (tensorVector h f)
  map_add' f g := by
    rw [← map_add]
    congr 1
    ext i
    simp [smul_add]
  map_smul' c f := by
    rw [← map_smul]
    congr 1
    ext i
    simp [smul_smul, mul_comm]

@[simp] theorem norm_vectorCreationLinear (h : OneParticleSpace I) (f : WordSpace I) :
    ‖vectorCreationLinear h f‖ = ‖h‖ * ‖f‖ := by
  change ‖creationFamilyIsometry (tensorVector h f)‖ = _
  rw [LinearIsometry.norm_map, norm_tensorVector]

/-- The actual bounded left creation operator for an arbitrary one-particle vector. -/
def vectorCreation (h : OneParticleSpace I) : WordSpace I →L[ℂ] WordSpace I :=
  (vectorCreationLinear h).mkContinuous ‖h‖ (fun f => (norm_vectorCreationLinear h f).le)

@[simp] theorem norm_vectorCreation_apply (h : OneParticleSpace I) (f : WordSpace I) :
    ‖vectorCreation h f‖ = ‖h‖ * ‖f‖ := norm_vectorCreationLinear h f

/-- Annihilation for an arbitrary one-particle vector is the actual Hilbert adjoint. -/
def vectorAnnihilation (h : OneParticleSpace I) : WordSpace I →L[ℂ] WordSpace I :=
  (vectorCreation h).adjoint

/-- Covariance factorization for arbitrary left creation operators. -/
theorem inner_vectorCreation (h k : OneParticleSpace I) (f g : WordSpace I) :
    inner ℂ (vectorCreation h f) (vectorCreation k g) = inner ℂ h k * inner ℂ f g := by
  change inner ℂ (creationFamilyIsometry (tensorVector h f))
    (creationFamilyIsometry (tensorVector k g)) = _
  rw [LinearIsometry.inner_map_map, inner_tensorVector]

/-- The canonical relation holds for every pair of square-summable one-particle vectors. -/
theorem vectorAnnihilation_creation (h k : OneParticleSpace I) :
    vectorAnnihilation h * vectorCreation k =
      inner ℂ h k • (1 : WordSpace I →L[ℂ] WordSpace I) := by
  apply ContinuousLinearMap.ext
  intro g
  apply ext_inner_left ℂ
  intro f
  change inner ℂ f ((vectorCreation h).adjoint (vectorCreation k g)) = inner ℂ f ((inner ℂ h k) • g)
  rw [ContinuousLinearMap.adjoint_inner_right, inner_vectorCreation, inner_smul_right]

@[simp] theorem norm_vectorCreation (h : OneParticleSpace I) : ‖vectorCreation h‖ = ‖h‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg h)
    intro f
    exact (norm_vectorCreation_apply h f).le
  · have hbound := (vectorCreation h).le_opNorm (vacuum : WordSpace I)
    simpa using hbound

@[simp] theorem norm_vectorAnnihilation (h : OneParticleSpace I) : ‖vectorAnnihilation h‖ = ‖h‖ := by
  rw [vectorAnnihilation, ContinuousLinearMap.adjoint.norm_map, norm_vectorCreation]

/-- The arbitrary-vector construction agrees with the previously proved basis creation. -/
@[simp] theorem vectorCreation_single (i : I) :
    vectorCreation (lp.single 2 i (1 : ℂ)) = creation i := by
  apply ContinuousLinearMap.ext
  intro f
  have ht : tensorVector (lp.single 2 i (1 : ℂ)) f = lp.single 2 i f := by
    ext j
    simp only [tensorVector_apply, lp.single_apply, Pi.single_apply]
    by_cases h : j = i <;> simp [h]
  change orthogonal_creationFamily.linearIsometry (tensorVector (lp.single 2 i (1 : ℂ)) f) = _
  rw [ht, OrthogonalFamily.linearIsometry_apply_single]
  rfl

/-- Creation is linear in the one-particle vector. -/
theorem vectorCreation_add (h k : OneParticleSpace I) :
    vectorCreation (h + k) = vectorCreation h + vectorCreation k := by
  apply ContinuousLinearMap.ext
  intro f
  change creationFamilyIsometry (tensorVector (h + k) f) =
    creationFamilyIsometry (tensorVector h f) + creationFamilyIsometry (tensorVector k f)
  rw [← map_add]
  congr 1
  ext i
  simp [add_smul]

theorem vectorCreation_smul (c : ℂ) (h : OneParticleSpace I) :
    vectorCreation (c • h) = c • vectorCreation h := by
  apply ContinuousLinearMap.ext
  intro f
  change creationFamilyIsometry (tensorVector (c • h) f) =
    c • creationFamilyIsometry (tensorVector h f)
  rw [← map_smul]
  congr 1
  ext i
  simp [smul_smul]

/-- A linear isometric embedding of all one-particle vectors into bounded creation operators. -/
def vectorCreationIsometry : OneParticleSpace I →ₗᵢ[ℂ] (WordSpace I →L[ℂ] WordSpace I) where
  toFun := vectorCreation
  map_add' := vectorCreation_add
  map_smul' := vectorCreation_smul
  norm_map' := norm_vectorCreation

/-- Arbitrary creation ranges are orthogonal to the vacuum, including infinite amplitudes. -/
theorem inner_vacuum_vectorCreation (h : OneParticleSpace I) (f : WordSpace I) :
    inner ℂ (vacuum : WordSpace I) (vectorCreation h f) = 0 := by
  have hs := orthogonal_creationFamily.hasSum_linearIsometry (tensorVector h f)
  have hi := (innerSL ℂ (vacuum : WordSpace I)).hasSum hs
  have hterm (i : I) : inner ℂ (vacuum : WordSpace I)
      (creationIsometry i (tensorVector h f i)) = 0 := by
    change inner ℂ vacuum (creation i (tensorVector h f i)) = 0
    rw [← ContinuousLinearMap.adjoint_inner_left]
    change inner ℂ (annihilation i vacuum) (tensorVector h f i) = 0
    simp
  simp only [innerSL_apply_apply, hterm] at hi
  exact hi.unique hasSum_zero

@[simp] theorem vectorAnnihilation_vacuum (h : OneParticleSpace I) :
    vectorAnnihilation h (vacuum : WordSpace I) = 0 := by
  apply ext_inner_left ℂ
  intro f
  rw [vectorAnnihilation, ContinuousLinearMap.adjoint_inner_right, inner_zero_right]
  rw [← inner_conj_symm, inner_vacuum_vectorCreation]
  simp

/-- The one-particle space embeds isometrically as the vectors created from the vacuum. -/
def oneParticleEmbedding : OneParticleSpace I →ₗᵢ[ℂ] WordSpace I where
  toFun h := vectorCreation h vacuum
  map_add' h k := by rw [vectorCreation_add]; rfl
  map_smul' c h := by rw [vectorCreation_smul]; rfl
  norm_map' h := by simp

@[simp] theorem oneParticleEmbedding_single (i : I) :
    oneParticleEmbedding (lp.single 2 i (1 : ℂ)) = word [i] := by
  change vectorCreation (lp.single 2 i (1 : ℂ)) vacuum = _
  rw [vectorCreation_single]
  exact creation_word i []

end FreeProbability.Fock



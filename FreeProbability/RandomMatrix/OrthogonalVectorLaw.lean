import FreeProbability.RandomMatrix.OrthogonalTransitivity
import FreeProbability.RandomMatrix.OrthogonalLinearMoment

/-! # Haar images of vectors of equal Euclidean norm -/

namespace FreeProbability.Orthogonal

open Matrix MeasureTheory

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Interpret a genuine real orthogonal matrix as a Euclidean isometry. -/
noncomputable def toLinearIsometryEquiv (U : Group n) :
    EuclideanSpace ℝ n ≃ₗᵢ[ℝ] EuclideanSpace ℝ n :=
  Unitary.linearIsometryEquiv
    (Unitary.map (StarMonoidHom.ofClass (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ))) U)

theorem toLinearIsometryEquiv_apply (U : Group n) (v : EuclideanSpace ℝ n) :
    toLinearIsometryEquiv U v = WithLp.toLp 2 ((U : Matrix n n ℝ) *ᵥ WithLp.ofLp v) := by
  rfl

theorem norm_mulVec (U : Group n) (x : n → ℝ) :
    ‖WithLp.toLp 2 ((U : Matrix n n ℝ) *ᵥ x)‖ = ‖WithLp.toLp 2 x‖ :=
  (toLinearIsometryEquiv U).norm_map (WithLp.toLp 2 x)

theorem continuous_mulVec (x : n → ℝ) :
    Continuous (fun U : Group n => (U : Matrix n n ℝ) *ᵥ x) := by
  apply continuous_pi
  intro i
  apply continuous_finsetSum
  intro j _
  have hc : Continuous (fun U : Group n => U i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
  exact hc.mul continuous_const

theorem continuous_action :
    Continuous (fun p : Group n × (n → ℝ) => (p.1 : Matrix n n ℝ) *ᵥ p.2) := by
  apply continuous_pi
  intro i
  apply continuous_finsetSum
  intro j _
  have hc : Continuous (fun U : Group n => U i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
  exact (hc.comp continuous_fst).mul ((continuous_apply j).comp continuous_snd)

noncomputable def vectorLaw (x : n → ℝ) : Measure (n → ℝ) :=
  (haar n).map (fun U : Group n => (U : Matrix n n ℝ) *ᵥ x)

instance vectorLaw_isProbabilityMeasure (x : n → ℝ) : IsProbabilityMeasure (vectorLaw x) := by
  unfold vectorLaw
  exact (Measure.isProbabilityMeasure_map_iff (continuous_mulVec x).aemeasurable).mpr inferInstance

theorem vectorLaw_eq_of_norm_eq (x y : n → ℝ)
    (hxy : ‖WithLp.toLp 2 x‖ = ‖WithLp.toLp 2 y‖) : vectorLaw x = vectorLaw y := by
  obtain ⟨V, hV⟩ := exists_mulVec_eq_of_norm_eq x y hxy
  have he : (fun U : Group n => (U : Matrix n n ℝ) *ᵥ y) =
      (fun U : Group n => ((U * V : Group n) : Matrix n n ℝ) *ᵥ x) := by
    funext U
    rw [← hV, Matrix.mulVec_mulVec]
    rfl
  unfold vectorLaw
  rw [he]
  have hm := Measure.map_map (continuous_mulVec x).measurable (measurable_mul_const V)
    (μ := haar n)
  simp only [Function.comp_def, map_mul_right_eq_self] at hm
  exact hm

theorem vectorLaw_map_mulVec (V : Group n) (x : n → ℝ) :
    (vectorLaw x).map (fun y => (V : Matrix n n ℝ) *ᵥ y) = vectorLaw x := by
  have hv : Measurable (fun y => (V : Matrix n n ℝ) *ᵥ y) := by
    apply Continuous.measurable
    apply continuous_pi
    intro i
    apply continuous_finsetSum
    intro j _
    exact continuous_const.mul (continuous_apply j)
  unfold vectorLaw
  rw [Measure.map_map hv (continuous_mulVec x).measurable]
  have he : ((fun y => (V : Matrix n n ℝ) *ᵥ y) ∘
      (fun U : Group n => (U : Matrix n n ℝ) *ᵥ x)) =
        (fun U : Group n => ((V * U : Group n) : Matrix n n ℝ) *ᵥ x) := by
    funext U
    simp only [Function.comp_apply, Matrix.mulVec_mulVec]
    rfl
  rw [he]
  have hm := Measure.map_map (continuous_mulVec x).measurable (measurable_const_mul V)
    (μ := haar n)
  simp only [Function.comp_def, map_mul_left_eq_self] at hm
  exact hm.symm

theorem vectorLaw_sphere (x : n → ℝ) :
    vectorLaw x {y | ‖WithLp.toLp 2 y‖ = ‖WithLp.toLp 2 x‖} = 1 := by
  have hc : Continuous (fun y : n → ℝ => ‖WithLp.toLp 2 y‖) := by fun_prop
  have hs : MeasurableSet {y : n → ℝ | ‖WithLp.toLp 2 y‖ = ‖WithLp.toLp 2 x‖} :=
    (isClosed_eq hc continuous_const).measurableSet
  rw [vectorLaw, Measure.map_apply (continuous_mulVec x).measurable hs]
  simp [Set.preimage, norm_mulVec]

theorem vectorLaw_map_smul (a : ℝ) (x : n → ℝ) :
    (vectorLaw x).map (fun y => a • y) = vectorLaw (a • x) := by
  have hm : Measurable (fun y : n → ℝ => a • y) := by
    apply Continuous.measurable
    exact continuous_id.const_smul a
  unfold vectorLaw
  rw [Measure.map_map hm (continuous_mulVec x).measurable]
  congr 1
  funext U
  simp [Matrix.mulVec_smul]

theorem integral_rowLinearForm_pow_eq_of_norm_eq (x y : n → ℝ) (r : n) (k : ℕ)
    (hxy : ‖WithLp.toLp 2 x‖ = ‖WithLp.toLp 2 y‖) :
    (∫ U : Group n, rowLinearForm x r U ^ k ∂haar n) =
      ∫ U : Group n, rowLinearForm y r U ^ k ∂haar n := by
  have hx : Measurable (fun U : Group n => (U : Matrix n n ℝ) *ᵥ x) := (continuous_mulVec x).measurable
  have hy : Measurable (fun U : Group n => (U : Matrix n n ℝ) *ᵥ y) := (continuous_mulVec y).measurable
  have hf : AEStronglyMeasurable (fun v : n → ℝ => v r ^ k) (vectorLaw x) :=
    ((continuous_apply r).pow k).aestronglyMeasurable
  have hf' : AEStronglyMeasurable (fun v : n → ℝ => v r ^ k) (vectorLaw y) :=
    ((continuous_apply r).pow k).aestronglyMeasurable
  have hxm := integral_map hx.aemeasurable hf
  have hym := integral_map hy.aemeasurable hf'
  change (∫ v, v r ^ k ∂vectorLaw x) = _ at hxm
  change (∫ v, v r ^ k ∂vectorLaw y) = _ at hym
  change (∫ U : Group n, ((U : Matrix n n ℝ) *ᵥ x) r ^ k ∂haar n) =
    ∫ U : Group n, ((U : Matrix n n ℝ) *ᵥ y) r ^ k ∂haar n
  rw [← hxm, ← hym, vectorLaw_eq_of_norm_eq x y hxy]

end FreeProbability.Orthogonal

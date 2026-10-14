import FreeProbability.RandomMatrix.OrthogonalSphereUniqueness
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! # Gaussian representation of a Haar direction -/

namespace FreeProbability.Orthogonal

open Matrix MeasureTheory ProbabilityTheory

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Independent standard real Gaussian coordinates. -/
noncomputable def gaussianVector (n : Type*) [Fintype n] : Measure (n → ℝ) :=
  Measure.pi (fun _ : n => gaussianReal 0 1)

instance gaussianVector_isProbabilityMeasure : IsProbabilityMeasure (gaussianVector n) := by
  unfold gaussianVector
  infer_instance

/-- Normalize using the Euclidean norm. The value at zero is explicitly zero. -/
noncomputable def direction (x : n → ℝ) : n → ℝ := ‖WithLp.toLp 2 x‖⁻¹ • x

omit [DecidableEq n] in
theorem measurable_direction : Measurable (direction (n := n)) := by
  have hc : Continuous (fun x : n → ℝ => ‖WithLp.toLp 2 x‖) := by fun_prop
  exact hc.measurable.inv.smul measurable_id

omit [DecidableEq n] in
@[simp] theorem direction_zero : direction (0 : n → ℝ) = 0 := by simp [direction]

omit [DecidableEq n] in
theorem norm_direction (x : n → ℝ) (hx : x ≠ 0) : ‖WithLp.toLp 2 (direction x)‖ = 1 := by
  have hn : ‖WithLp.toLp 2 x‖ ≠ 0 := norm_ne_zero_iff.mpr (by simpa using hx)
  simp [direction, WithLp.toLp_smul, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hn]

theorem direction_mulVec (U : Group n) (x : n → ℝ) :
    direction ((U : Matrix n n ℝ) *ᵥ x) = (U : Matrix n n ℝ) *ᵥ direction x := by
  simp only [direction, norm_mulVec, Matrix.mulVec_smul]

omit [DecidableEq n] in
theorem gaussianVector_zero [Nonempty n] : gaussianVector n {(0 : n → ℝ)} = 0 := by
  let _ : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  simp [gaussianVector]

theorem gaussianVector_map_mulVec (U : Group n) :
    (gaussianVector n).map (fun x => (U : Matrix n n ℝ) *ᵥ x) = gaussianVector n := by
  have hto : Measurable (WithLp.toLp 2 : (n → ℝ) → EuclideanSpace ℝ n) :=
    (PiLp.continuous_toLp 2 (fun _ : n => ℝ)).measurable
  have hof : Measurable (WithLp.ofLp : EuclideanSpace ℝ n → (n → ℝ)) :=
    (PiLp.continuous_ofLp 2 (fun _ : n => ℝ)).measurable
  have hgauss : (gaussianVector n).map (WithLp.toLp 2) = stdGaussian (EuclideanSpace ℝ n) :=
    map_pi_eq_stdGaussian
  have hback : (stdGaussian (EuclideanSpace ℝ n)).map WithLp.ofLp = gaussianVector n := by
    rw [← hgauss, Measure.map_map hof hto]
    simp [Function.comp_def]
  have hU : Measurable (fun x => (U : Matrix n n ℝ) *ᵥ x) :=
    (continuous_action.comp (continuous_const.prodMk continuous_id)).measurable
  have he : ((fun x => (U : Matrix n n ℝ) *ᵥ x) ∘ WithLp.ofLp) =
      (WithLp.ofLp ∘ toLinearIsometryEquiv U) := by
    funext v
    simp [toLinearIsometryEquiv_apply]
  calc
    _ = ((stdGaussian (EuclideanSpace ℝ n)).map WithLp.ofLp).map
        (fun x => (U : Matrix n n ℝ) *ᵥ x) := by rw [hback]
    _ = (stdGaussian (EuclideanSpace ℝ n)).map
        (WithLp.ofLp ∘ toLinearIsometryEquiv U) := by rw [Measure.map_map hU hof, he]
    _ = ((stdGaussian (EuclideanSpace ℝ n)).map (toLinearIsometryEquiv U)).map WithLp.ofLp := by
      rw [Measure.map_map hof (toLinearIsometryEquiv U).continuous.measurable]
    _ = (stdGaussian (EuclideanSpace ℝ n)).map WithLp.ofLp := by rw [stdGaussian_map]
    _ = _ := hback

noncomputable def gaussianDirection (n : Type*) [Fintype n] : Measure (n → ℝ) :=
  (gaussianVector n).map direction

instance gaussianDirection_isProbabilityMeasure : IsProbabilityMeasure (gaussianDirection n) := by
  unfold gaussianDirection
  infer_instance

theorem gaussianDirection_map_mulVec (U : Group n) :
    (gaussianDirection n).map (fun x => (U : Matrix n n ℝ) *ᵥ x) = gaussianDirection n := by
  have hU : Measurable (fun x => (U : Matrix n n ℝ) *ᵥ x) :=
    (continuous_action.comp (continuous_const.prodMk continuous_id)).measurable
  unfold gaussianDirection
  rw [Measure.map_map hU measurable_direction]
  have he : ((fun x => (U : Matrix n n ℝ) *ᵥ x) ∘ direction) =
      (direction ∘ (fun x => (U : Matrix n n ℝ) *ᵥ x)) := by
    funext x
    exact (direction_mulVec U x).symm
  rw [he]
  have hm := Measure.map_map measurable_direction hU (μ := gaussianVector n)
  rw [gaussianVector_map_mulVec] at hm
  exact hm.symm

omit [DecidableEq n] in
theorem gaussianDirection_ae_norm_one [Nonempty n] :
    ∀ᵐ x ∂gaussianDirection n, ‖WithLp.toLp 2 x‖ = 1 := by
  have ha0 : ∀ᵐ x ∂gaussianVector n, x ≠ 0 := by
    rw [ae_iff]
    have he : {x : n → ℝ | ¬x ≠ 0} = {0} := by ext x; simp
    rw [he, gaussianVector_zero]
  have ha : ∀ᵐ x ∂gaussianVector n, ‖WithLp.toLp 2 (direction x)‖ = 1 :=
    ha0.mono (fun x hx => norm_direction x hx)
  have hc : Continuous (fun x : n → ℝ => ‖WithLp.toLp 2 x‖) := by fun_prop
  have hs : MeasurableSet {x : n → ℝ | ‖WithLp.toLp 2 x‖ = 1} :=
    (isClosed_eq hc continuous_const).measurableSet
  exact (ae_map_iff measurable_direction.aemeasurable hs).mpr ha

/-- Normalized independent Gaussian coordinates have the complete Haar image law
of every unit Euclidean input, rather than only matching finitely many moments. -/
theorem gaussianDirection_eq_vectorLaw [Nonempty n] (x : n → ℝ)
    (hx : ‖WithLp.toLp 2 x‖ = 1) : gaussianDirection n = vectorLaw x := by
  apply eq_vectorLaw_of_invariant_sphere
  · simpa only [hx] using (gaussianDirection_ae_norm_one (n := n))
  · exact gaussianDirection_map_mulVec

/-- Full Gaussian representation of every Haar image, with its input length
restored. The equality holds at zero input as well. -/
theorem vectorLaw_eq_normalized_gaussian [Nonempty n] (x : n → ℝ) :
    vectorLaw x = (gaussianVector n).map (fun g => ‖WithLp.toLp 2 x‖ • direction g) := by
  classical
  let r : n := Classical.choice inferInstance
  let e : n → ℝ := Pi.single r 1
  have he : ‖WithLp.toLp 2 e‖ = 1 := by
    simp [e]
  have hg : gaussianDirection n = vectorLaw e := gaussianDirection_eq_vectorLaw e he
  have hr : ‖WithLp.toLp 2 (‖WithLp.toLp 2 x‖ • e)‖ = ‖WithLp.toLp 2 x‖ := by
    rw [WithLp.toLp_smul, norm_smul, Real.norm_of_nonneg (norm_nonneg _), he, mul_one]
  have hm : Measurable (fun y : n → ℝ => ‖WithLp.toLp 2 x‖ • y) :=
    (continuous_id.const_smul ‖WithLp.toLp 2 x‖).measurable
  symm
  calc
    _ = (gaussianDirection n).map (fun y => ‖WithLp.toLp 2 x‖ • y) := by
      rw [gaussianDirection, Measure.map_map hm measurable_direction]
      rfl
    _ = vectorLaw (‖WithLp.toLp 2 x‖ • e) := by rw [hg, vectorLaw_map_smul]
    _ = vectorLaw x := vectorLaw_eq_of_norm_eq _ x hr

end FreeProbability.Orthogonal

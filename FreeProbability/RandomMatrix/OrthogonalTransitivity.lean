import FreeProbability.RandomMatrix.OrthogonalHaar
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Orthogonal transitivity on Euclidean spheres -/

namespace FreeProbability.Orthogonal

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The actual orthogonal matrix of a Euclidean linear isometry. -/
noncomputable def ofLinearIsometryEquiv
    (f : EuclideanSpace ℝ n ≃ₗᵢ[ℝ] EuclideanSpace ℝ n) : Group n :=
  ⟨f.toMatrix (EuclideanSpace.basisFun n ℝ).toBasis (EuclideanSpace.basisFun n ℝ).toBasis, by
    apply (Matrix.mem_orthogonalGroup_iff n ℝ).mpr
    have h := (Matrix.mem_unitaryGroup_iff).mp
      (f.toMatrix_mem_unitaryGroup (EuclideanSpace.basisFun n ℝ) (EuclideanSpace.basisFun n ℝ))
    simpa [star_eq_conjTranspose] using h⟩

theorem ofLinearIsometryEquiv_mulVec
    (f : EuclideanSpace ℝ n ≃ₗᵢ[ℝ] EuclideanSpace ℝ n) (x : n → ℝ) :
    (ofLinearIsometryEquiv f : Matrix n n ℝ) *ᵥ x = WithLp.ofLp (f (WithLp.toLp 2 x)) := by
  have h := LinearMap.toMatrix_mulVec_repr (EuclideanSpace.basisFun n ℝ).toBasis
    (EuclideanSpace.basisFun n ℝ).toBasis f.toLinearEquiv.toLinearMap (WithLp.toLp 2 x)
  have hr (v : EuclideanSpace ℝ n) :
      (fun i => (EuclideanSpace.basisFun n ℝ).toBasis.repr v i) = WithLp.ofLp v := by
    funext i
    rw [OrthonormalBasis.coe_toBasis_repr_apply]
    rfl
  simpa only [ofLinearIsometryEquiv, hr, WithLp.ofLp_toLp,
    LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv] using h

/-- Equal Euclidean norms imply an actual orthogonal matrix carrying one vector
to the other. Reflection supplies the isometry even when both vectors vanish. -/
theorem exists_mulVec_eq_of_norm_eq (x y : n → ℝ)
    (hxy : ‖WithLp.toLp 2 x‖ = ‖WithLp.toLp 2 y‖) :
    ∃ U : Group n, (U : Matrix n n ℝ) *ᵥ x = y := by
  let v := WithLp.toLp 2 x
  let w := WithLp.toLp 2 y
  let f : EuclideanSpace ℝ n ≃ₗᵢ[ℝ] EuclideanSpace ℝ n :=
    (ℝ ∙ (v - w))ᗮ.reflection
  refine ⟨ofLinearIsometryEquiv f, ?_⟩
  rw [ofLinearIsometryEquiv_mulVec]
  have h := Submodule.reflection_sub hxy
  simpa [f, v, w] using congrArg WithLp.ofLp h

end FreeProbability.Orthogonal

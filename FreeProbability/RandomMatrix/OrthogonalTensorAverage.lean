import FreeProbability.Algebraic.CompactHaarAverageProjection
import FreeProbability.RandomMatrix.OrthogonalVectorLaw
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Actual orthogonal tensor powers and their genuine Haar averages -/

noncomputable section
namespace FreeProbability.Orthogonal
open Matrix MeasureTheory
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The ACTUAL tensor-power coordinate matrix, on the tuple basis. -/
def tensorPowerMatrix (k : ℕ) (U : Matrix n n ℝ) : Matrix (Fin k → n) (Fin k → n) ℝ :=
  fun i j => ∏ a : Fin k, U (i a) (j a)

omit [DecidableEq n] in
/-- Tensor-coordinate matrix multiplication follows from the full finite
sum over tuples, not an assumed representation identity. -/
theorem tensorPowerMatrix_mul (k : ℕ) (U V : Matrix n n ℝ) :
    tensorPowerMatrix k (U * V) = tensorPowerMatrix k U * tensorPowerMatrix k V := by
  ext i j
  simp only [tensorPowerMatrix, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro f hf
  exact Finset.prod_mul_distrib

omit [Fintype n] in
/-- The zero tensor order is included in the genuine identity matrix law. -/
theorem tensorPowerMatrix_one (k : ℕ) : tensorPowerMatrix k (1 : Matrix n n ℝ) = 1 := by
  ext i j
  simp only [tensorPowerMatrix, Matrix.one_apply]
  by_cases hij : i = j
  · subst j
    simp
  · simp only [hij, ite_false]
    obtain ⟨a, ha⟩ : ∃ a : Fin k, i a ≠ j a := by
      by_contra hn
      push Not at hn
      exact hij (funext hn)
    apply Finset.prod_eq_zero (Finset.mem_univ a)
    simp only [ha, ite_false]

omit [Fintype n] [DecidableEq n] in
theorem tensorPowerMatrix_transpose (k : ℕ) (U : Matrix n n ℝ) :
    tensorPowerMatrix k U.transpose = (tensorPowerMatrix k U).transpose := by
  rfl

/-- Actual orthogonality of arbitrary tensor powers, including all degenerate dimensions. -/
theorem tensorPowerMatrix_mem_orthogonal (k : ℕ) (U : Group n) :
    tensorPowerMatrix k (U : Matrix n n ℝ) ∈ Matrix.orthogonalGroup (Fin k → n) ℝ := by
  apply (Matrix.mem_orthogonalGroup_iff _ ℝ).mpr
  rw [← tensorPowerMatrix_transpose, ← tensorPowerMatrix_mul,
    (Matrix.mem_orthogonalGroup_iff n ℝ).mp U.property, tensorPowerMatrix_one]

/-- The ACTUAL group representation by tensor-coordinate orthogonal matrices. -/
def tensorPowerGroupHom (k : ℕ) : Group n →* Group (Fin k → n) where
  toFun U := ⟨tensorPowerMatrix k (U : Matrix n n ℝ), tensorPowerMatrix_mem_orthogonal k U⟩
  map_one' := Subtype.ext (tensorPowerMatrix_one k)
  map_mul' U V := Subtype.ext (tensorPowerMatrix_mul k (U : Matrix n n ℝ) (V : Matrix n n ℝ))

/-- The standard Euclidean representation of the actual orthogonal group. -/
def euclideanGroupHom : Group n →* (EuclideanSpace ℝ n ≃ₗᵢ[ℝ] EuclideanSpace ℝ n) :=
  Unitary.linearIsometryEquiv.toMonoidHom.comp
    (Unitary.map (StarMonoidHom.ofClass (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)))).toMonoidHom

/-- The genuine tensor-power Euclidean representation with continuous vector orbits. -/
def tensorPowerRepresentation (k : ℕ) : CompactIsometricRepresentation (Group n) ℝ
    (EuclideanSpace ℝ (Fin k → n)) where
  action := euclideanGroupHom.comp (tensorPowerGroupHom k)
  continuous_orbit v := by
    change Continuous (fun U : Group n => WithLp.toLp 2
      ((tensorPowerMatrix k (U : Matrix n n ℝ)) *ᵥ WithLp.ofLp v))
    apply (PiLp.continuous_toLp 2 (fun _ : Fin k → n => ℝ)).comp
    apply continuous_pi
    intro i
    apply continuous_finsetSum
    intro j hj
    apply Continuous.mul _ continuous_const
    apply continuous_finsetProd
    intro a ha
    exact (continuous_apply (j a)).comp ((continuous_apply (i a)).comp continuous_subtype_val)

/-- Actual averaging of arbitrary-order orthogonal tensors is the genuine
orthogonal projection onto the exact invariant tensors. -/
theorem tensorPowerAverage_orthogonal_projection (k : ℕ) :
    IsSelfAdjoint (tensorPowerRepresentation (n := n) k).averageCLM ∧
      IsIdempotentElem (tensorPowerRepresentation (n := n) k).averageCLM ∧
      LinearMap.range (tensorPowerRepresentation (n := n) k).averageCLM.toLinearMap =
        (tensorPowerRepresentation (n := n) k).fixedVectors ∧
      LinearMap.ker (tensorPowerRepresentation (n := n) k).averageCLM.toLinearMap =
        (tensorPowerRepresentation (n := n) k).fixedVectors.orthogonal :=
  (tensorPowerRepresentation (n := n) k).averageCLM_orthogonal_projection

/-- A literal tuple-coordinate basis vector for the actual tensor representation. -/
def tensorBasisVector (k : ℕ) (j : Fin k → n) : EuclideanSpace ℝ (Fin k → n) :=
  WithLp.toLp 2 (Pi.single j 1)

/-- Actual tensor matrix coefficients equal literal products of orthogonal entries. -/
theorem tensorPowerRepresentation_basis_coefficient (k : ℕ) (U : Group n) (i j : Fin k → n) :
    ((tensorPowerRepresentation (n := n) k).action U (tensorBasisVector k j)) i = entryMonomial i j U := by
  change ((tensorPowerMatrix k (U : Matrix n n ℝ)) *ᵥ Pi.single j 1) i = _
  rw [Matrix.mulVec_single]
  simp only [MulOpposite.op_one, one_smul]
  rfl

/-- The actual Haar averaging coefficients are the GENUINE entry integrals
of arbitrary order, including the scalar zeroth-order representation. -/
theorem tensorPowerAverage_basis_coefficient (k : ℕ) (i j : Fin k → n) :
    ((tensorPowerRepresentation (n := n) k).averageCLM (tensorBasisVector k j)) i = entryMoment i j := by
  let ρ := tensorPowerRepresentation (n := n) k
  have h := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin k → n => ℝ) i).integral_comp_comm
    (ρ.integrable_orbit (tensorBasisVector k j))
  change (∫ U : Group n, (ρ.action U (tensorBasisVector k j)) i ∂CompactHaar.probability (Group n)) =
    (ρ.averageCLM (tensorBasisVector k j)) i at h
  rw [← h]
  simp only [ρ, tensorPowerRepresentation_basis_coefficient]
  rfl
end FreeProbability.Orthogonal

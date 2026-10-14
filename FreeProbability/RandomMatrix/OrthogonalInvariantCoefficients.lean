import FreeProbability.RandomMatrix.OrthogonalPairingInvertible
import FreeProbability.RandomMatrix.OrthogonalPlaneMixing

/-! # Genuine coefficient constraints of actual invariant orthogonal tensors -/

noncomputable section
open scoped Classical
namespace FreeProbability.Orthogonal
open Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Literal coordinate action of the ACTUAL tensor representation. -/
theorem tensorPower_action_coefficient (k : ℕ) (U : Group n)
    (v : EuclideanSpace ℝ (Fin k → n)) (i : Fin k → n) :
    ((tensorPowerRepresentation (n := n) k).action U v) i =
      ∑ j : Fin k → n, (∏ a : Fin k, U (i a) (j a)) * v j := rfl

/-- The actual tensor action of a coordinate reflection is the parity sign. -/
theorem tensorPower_reflection_coefficient (k : ℕ) (c : n)
    (v : EuclideanSpace ℝ (Fin k → n)) (i : Fin k → n) :
    ((tensorPowerRepresentation (n := n) k).action (coordinateReflection c) v) i =
      (-1 : ℝ) ^ (Finset.univ.filter (fun a => i a = c)).card * v i := by
  rw [tensorPower_action_coefficient]
  have ht (j : Fin k → n) :
      (∏ a : Fin k, (coordinateReflection c) (i a) (j a)) =
      (-1 : ℝ) ^ (Finset.univ.filter (fun a => i a = c)).card *
        tensorPowerMatrix k (1 : Matrix n n ℝ) i j := by
    simpa only [mul_one, entryMonomial, tensorPowerMatrix, Submonoid.coe_one] using entryMonomial_reflection i j c (1 : Group n)
  simp_rw [ht, tensorPowerMatrix_one]
  simp [Matrix.one_apply, mul_ite, ite_mul]

/-- Fixedness forces the ACTUAL reflection parity equation for every tuple. -/
theorem invariantTensor_reflection {k : ℕ} (v : EuclideanSpace ℝ (Fin k → n))
    (hv : v ∈ (tensorPowerRepresentation (n := n) k).fixedVectors) (i : Fin k → n) (c : n) :
    (-1 : ℝ) ^ (Finset.univ.filter (fun a => i a = c)).card * v i = v i := by
  have he := congrArg (fun w : EuclideanSpace ℝ (Fin k → n) => w i) (hv (coordinateReflection c))
  simpa only [tensorPower_reflection_coefficient] using he

/-- Any color of odd multiplicity forces the ACTUAL invariant coefficient to vanish. -/
theorem invariantTensor_coefficient_eq_zero_of_odd_count {k : ℕ}
    (v : EuclideanSpace ℝ (Fin k → n))
    (hv : v ∈ (tensorPowerRepresentation (n := n) k).fixedVectors) (i : Fin k → n) (c : n)
    (hc : Odd (Finset.univ.filter (fun a => i a = c)).card) : v i = 0 := by
  have he := invariantTensor_reflection v hv i c
  rw [hc.neg_one_pow, neg_one_mul] at he
  linarith

/-- A genuine coordinate permutation acts by relabeling the entire tuple. -/
theorem tensorPower_permutation_coefficient (k : ℕ) (σ : Equiv.Perm n)
    (v : EuclideanSpace ℝ (Fin k → n)) (i : Fin k → n) :
    ((tensorPowerRepresentation (n := n) k).action (permutation σ) v) i =
      v (fun a => σ (i a)) := by
  rw [tensorPower_action_coefficient]
  have ht (j : Fin k → n) :
      (∏ a : Fin k, (permutation σ) (i a) (j a)) =
        tensorPowerMatrix k (1 : Matrix n n ℝ) (fun a => σ (i a)) j := by
    apply Finset.prod_congr rfl
    intro a ha
    have h := mul_permutation_apply (1 : Group n) σ (i a) (j a)
    simpa [Matrix.one_apply, Equiv.eq_symm_apply] using h
  simp_rw [ht, tensorPowerMatrix_one]
  simp [Matrix.one_apply, ite_mul]

/-- Actual fixed-tensor coefficients are invariant under arbitrary coordinate relabeling. -/
theorem invariantTensor_permutation {k : ℕ} (v : EuclideanSpace ℝ (Fin k → n))
    (hv : v ∈ (tensorPowerRepresentation (n := n) k).fixedVectors)
    (i : Fin k → n) (σ : Equiv.Perm n) : v (fun a => σ (i a)) = v i := by
  have he := congrArg (fun w : EuclideanSpace ℝ (Fin k → n) => w i) (hv (permutation σ))
  simpa only [tensorPower_permutation_coefficient] using he

/-- Genuine normalized plane mixing forces the full ACTUAL tensor coefficient
identity, with its explicit inverse-square-root-of-two coefficients. -/
theorem invariantTensor_planeMixer {k : ℕ} (v : EuclideanSpace ℝ (Fin k → n))
    (hv : v ∈ (tensorPowerRepresentation (n := n) k).fixedVectors)
    (i : Fin k → n) (c d : n) (hcd : c ≠ d) :
    (∑ j : Fin k → n, (∏ a : Fin k,
      planeMixerMatrix c d ((Real.sqrt 2)⁻¹) (i a) (j a)) * v j) = v i := by
  have he := congrArg (fun w : EuclideanSpace ℝ (Fin k → n) => w i) (hv (planeMixer c d hcd))
  simpa only [tensorPower_action_coefficient, planeMixer] using he
end FreeProbability.Orthogonal

import FreeProbability.RandomMatrix.OrthogonalPairingNetworkTransfer
import FreeProbability.RandomMatrix.OrthogonalPermutationNetworkNorm

/-! # Actual Euclidean transpose invariance and sharp pairing network bounds -/

noncomputable section
open scoped Classical Matrix.Norms.L2Operator
namespace FreeProbability.Orthogonal
open Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

private def conjugateVector (v : EuclideanSpace ℂ n) : EuclideanSpace ℂ n :=
  WithLp.toLp 2 (fun i => star (v i))

omit [DecidableEq n] in
private theorem norm_conjugateVector (v : EuclideanSpace ℂ n) : ‖conjugateVector v‖ = ‖v‖ := by
  simp only [PiLp.norm_eq_of_L2, conjugateVector, norm_star]

omit [Fintype n] [DecidableEq n] in
private theorem conjugateVector_involutive (v : EuclideanSpace ℂ n) :
    conjugateVector (conjugateVector v) = v := by
  apply PiLp.ext
  intro i
  simp [conjugateVector]

private def conjugateEntries (M : Matrix n n ℂ) : Matrix n n ℂ := fun i j => star (M i j)

private theorem conjugate_operator_apply (M : Matrix n n ℂ) (v : EuclideanSpace ℂ n) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (conjugateEntries M) (conjugateVector v) =
      conjugateVector (Matrix.toEuclideanCLM (𝕜 := ℂ) M v) := by
  apply PiLp.ext
  intro i
  change (∑ j, star (M i j) * star (v j)) = star (∑ j, M i j * v j)
  simp only [star_sum, star_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem conjugate_operator_norm_le (M : Matrix n n ℂ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (conjugateEntries M)‖ ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) M‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  have he := conjugate_operator_apply M (conjugateVector v)
  rw [conjugateVector_involutive] at he
  rw [he, norm_conjugateVector]
  exact (Matrix.toEuclideanCLM (𝕜 := ℂ) M).le_opNorm (conjugateVector v) |>.trans_eq
    (by rw [norm_conjugateVector])

private theorem conjugate_operator_norm (M : Matrix n n ℂ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (conjugateEntries M)‖ =
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) M‖ := by
  apply le_antisymm (conjugate_operator_norm_le M)
  have he := conjugate_operator_norm_le (conjugateEntries M)
  have hm : conjugateEntries (conjugateEntries M) = M := by ext i j; simp [conjugateEntries]
  rwa [hm] at he

/-- Complex transpose preserves the GENUINE Euclidean operator norm, including
empty matrix dimension. This does not use the entrywise matrix norm theorem. -/
theorem Euclidean_opNorm_transpose (M : Matrix n n ℂ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) M.transpose‖ = ‖Matrix.toEuclideanCLM (𝕜 := ℂ) M‖ := by
  have he : conjugateEntries M.conjTranspose = M.transpose := by
    ext i j
    simp [conjugateEntries, Matrix.conjTranspose_apply, Matrix.transpose_apply]
  rw [← he, conjugate_operator_norm]
  exact Matrix.l2_opNorm_conjTranspose M

/-- Actual edge orientations retain exactly the original operator norms. -/
theorem pairingOrientedMatrix_opNorm {r : ℕ} (p : OrdinaryPairing r) (e : PairingSites r)
    (M : Fin r → Matrix n n ℂ) (a : PairingHalfSites p (Quotient.mk _ e)) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (pairingOrientedMatrix p e M a)‖ =
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (M (e a.val).1)‖ := by
  unfold pairingOrientedMatrix
  split
  · rfl
  · exact Euclidean_opNorm_transpose _

/-- The true paired network has exactly one dimension factor per raw join
loop and one actual Euclidean operator norm per matrix edge. -/
theorem pairingNetwork_norm_le {r : ℕ} (p : OrdinaryPairing r) (e : PairingSites r)
    (M : Fin r → Matrix n n ℂ) :
    ‖pairingNetwork p e M‖ ≤ (Fintype.card n : ℝ) ^ pairingLoopCount p (Quotient.mk _ e) *
      ∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (M k)‖ := by
  rw [pairingNetwork_eq_oriented_permutationNetwork]
  apply (permutationNetwork_norm_le _ _).trans_eq
  rw [pairingHalf_orbit_card]
  simp_rw [pairingOrientedMatrix_opNorm]
  congr 1
  rw [← Equiv.prod_comp (pairingEdgeHalfEquiv p e)]
  apply Finset.prod_congr rfl
  intro k _
  rw [pairingEdgeHalfEquiv_apply, pairingSelectedEndpoint_coordinate]

/-- The existing actual column network inherits the sharp genuine loop-count
bound, with literal Euclidean operator norms. -/
theorem traceColumnNetwork_norm_le {r : ℕ} (A : Fin r → Matrix n n ℂ) (q : OrdinaryPairing r) :
    ‖traceColumnNetwork A q‖ ≤
      (Fintype.card n : ℝ) ^ pairingLoopCount q (Quotient.mk _ (traceColumnEdgeCode r)) *
        ∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A k)‖ := by
  rw [traceColumnNetwork_eq_pairingNetwork]
  exact pairingNetwork_norm_le _ _ _

omit [DecidableEq n] in
/-- Genuine transpose orientation also preserves ordinary complex trace. -/
theorem pairingOrientedMatrix_trace {r : ℕ} (p : OrdinaryPairing r) (e : PairingSites r)
    (M : Fin r → Matrix n n ℂ) (a : PairingHalfSites p (Quotient.mk _ e)) :
    Matrix.trace (pairingOrientedMatrix p e M a) = Matrix.trace (M (e a.val).1) := by
  unfold pairingOrientedMatrix
  split
  · rfl
  · exact Matrix.trace_transpose _

/-- Actual centered paired networks vanish if their genuine selected cycle
permutation has a fixed singleton. No scalar network cancellation is assumed. -/
theorem pairingNetwork_eq_zero_of_centered_fixed_cycle {r : ℕ} (p : OrdinaryPairing r)
    (e : PairingSites r) (M : Fin r → Matrix n n ℂ) (hM : ∀ k, Matrix.trace (M k) = 0)
    (a : PairingHalfSites p (Quotient.mk _ e))
    (ha : pairingHalfPermutation p (Quotient.mk _ e) a = a) : pairingNetwork p e M = 0 := by
  rw [pairingNetwork_eq_oriented_permutationNetwork]
  apply permutationNetwork_eq_zero_of_fixed_trace_zero _ _ a ha
  rw [pairingOrientedMatrix_trace]
  exact hM _

end FreeProbability.Orthogonal

import FreeProbability.OperatorValued.MatrixSemicircularModel
import FreeProbability.OperatorValued.MatrixWordExpansion
import FreeProbability.Fock.WickFormula

/-!
# The genuine matrix-valued free Wick formula

Actual products of matrix linear combinations of the constructed Fock operators
are evaluated by actual noncrossing pairings and Kronecker color covariances.
The matrix coefficient words retain their order. Arbitrary interspersed
coefficient matrices are included, not just powers of one random matrix.
-/

noncomputable section
open scoped Classical

namespace FreeProbability.Fock

open Matrix NoncrossingPairing

variable {I n : Type*} [Fintype I] [Fintype n] [DecidableEq n] {k : ℕ}

/-- Joint matrix Wick moments with arbitrary coordinate-dependent coefficient
arrays, in the actual Fock generated C-star probability space. -/
theorem closedMatrixSemicircular_joint_wick (C : Fin k → I → Matrix n n ℂ) :
    matrixExpectation (closedGeneratedVacuumState I).toProbabilitySpace
      (List.ofFn (fun j => closedMatrixSemicircular (C j))).prod =
      ∑ p : NoncrossingPairing k, ∑ f : Fin k → I,
        (∏ e ∈ pairingPairs p, if f e.1 = f e.2 then (1 : ℂ) else 0) •
          (List.ofFn (fun j => C j (f j))).prod := by
  change matrixExpectation (closedGeneratedVacuumState I).toProbabilitySpace
    (List.ofFn (fun j => matrixLinearCombination closedSemicircular (C j))).prod = _
  rw [matrixExpectation_word_expansion]
  simp_rw [closedGeneratedVacuumState_joint_free_wick, Finset.sum_smul]
  exact Finset.sum_comm

/-- The power moments of the actual Hermitian matrix semicircular sum are its
ordered coefficient-weighted noncrossing-pairing sum. -/
theorem closedMatrixSemicircular_pow_wick (C : I → Matrix n n ℂ) (k : ℕ) :
    matrixExpectation (closedGeneratedVacuumState I).toProbabilitySpace (closedMatrixSemicircular C ^ k) =
      ∑ p : NoncrossingPairing k, ∑ f : Fin k → I,
        (∏ e ∈ pairingPairs p, if f e.1 = f e.2 then (1 : ℂ) else 0) •
          (List.ofFn (fun j => C (f j))).prod := by
  simpa only [List.ofFn_const, List.prod_replicate] using
    closedMatrixSemicircular_joint_wick (fun _ : Fin k => C)

/-- The actual operator-valued Wick formula with arbitrary deterministic matrix
coefficients between successive copies of the matrix semicircular variable. -/
theorem closedMatrixSemicircular_interspersed_wick (C : I → Matrix n n ℂ)
    (D : Fin k → Matrix n n ℂ) :
    matrixExpectation (closedGeneratedVacuumState I).toProbabilitySpace
      (List.ofFn (fun j => closedMatrixSemicircular C * scalarMatrixEmbedding (D j))).prod =
      ∑ p : NoncrossingPairing k, ∑ f : Fin k → I,
        (∏ e ∈ pairingPairs p, if f e.1 = f e.2 then (1 : ℂ) else 0) •
          (List.ofFn (fun j => C (f j) * D j)).prod := by
  have he (j : Fin k) : closedMatrixSemicircular C * scalarMatrixEmbedding (D j) =
      closedMatrixSemicircular (fun i => C i * D j) :=
    matrixLinearCombination_mul_scalarMatrix _ _ _
  simp_rw [he]
  exact closedMatrixSemicircular_joint_wick (fun j i => C i * D j)

/-- Every odd actual matrix joint moment vanishes. -/
theorem closedMatrixSemicircular_joint_eq_zero_of_odd (C : Fin k → I → Matrix n n ℂ)
    (hk : Odd k) :
    matrixExpectation (closedGeneratedVacuumState I).toProbabilitySpace
      (List.ofFn (fun j => closedMatrixSemicircular (C j))).prod = 0 := by
  rw [closedMatrixSemicircular_joint_wick]
  let : IsEmpty (NoncrossingPairing k) := ⟨fun p => not_nonempty_of_odd hk ⟨p⟩⟩
  simp

end FreeProbability.Fock

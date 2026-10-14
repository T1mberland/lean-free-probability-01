import FreeProbability.Applications.ReLU.Triangular
import FreeProbability.Matrix.HermitianResolvent

/-!
# Operator-norm consequences of the triangular cavity reduction

These are deterministic statements about the explicitly defined blocks. They
complete the exterior secular norm criterion and monotonicity, independently of
the random adapted-basis construction and asymptotic cavity estimates.
-/

namespace FreeProbability.ReLU

open Matrix
open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem bulkGram_posSemidef (C : Matrix n n ℝ) : (bulkGram C).PosSemidef := by
  have h := posSemidef_conjTranspose_mul_self
    (fromBlocks C 0 0 (0 : Matrix Unit Unit ℝ))
  simpa [fromBlocks_transpose, fromBlocks_multiply, bulkGram] using h

theorem bulkGram_norm (C : Matrix n n ℝ) : ‖bulkGram C‖ = ‖C‖ ^ 2 := by
  have hC : (Cᵀ * C).IsHermitian := by simpa using isHermitian_conjTranspose_mul_self C
  rw [bulkGram, hermitian_norm_zero_extension hC]
  simpa [pow_two] using Matrix.l2_opNorm_conjTranspose_mul_self C

theorem cavitySecular_eq_resolventForm (C : Matrix n n ℝ) (c : n → ℝ) (a z : ℝ)
    (hz : ‖C‖ ^ 2 < z) :
    cavitySecular C c a z = realResolventForm (bulkGram C) (exceptionalVector c a) z := by
  have hC : (Cᵀ * C).IsHermitian := by simpa using isHermitian_conjTranspose_mul_self C
  have hn : ‖Cᵀ * C‖ = ‖C‖ ^ 2 := by
    simpa [pow_two] using Matrix.l2_opNorm_conjTranspose_mul_self C
  have hd := hermitian_resolvent_det_ne_zero hC z
    (fun i => (hermitian_eigenvalue_le_norm hC i).trans_lt (hn.symm ▸ hz))
  have hz0 : z ≠ 0 := (lt_of_le_of_lt (sq_nonneg ‖C‖) hz).ne'
  have hs := secular_bulkGram C c a z hd hz0
  change 1 - realResolventForm (bulkGram C) (exceptionalVector c a) z =
    1 - cavitySecular C c a z at hs
  linarith

theorem triangularMatrix_secular_iff_exterior (C : Matrix n n ℝ) (c : n → ℝ) (a z : ℝ)
    (hz : ‖C‖ ^ 2 < z) :
    IsMatrixEigenvalue ((triangularMatrix C c a)ᵀ * triangularMatrix C c a) z ↔
      cavitySecular C c a z = 1 := by
  have hC : (Cᵀ * C).IsHermitian := by simpa using isHermitian_conjTranspose_mul_self C
  have hn : ‖Cᵀ * C‖ = ‖C‖ ^ 2 := by
    simpa [pow_two] using Matrix.l2_opNorm_conjTranspose_mul_self C
  exact triangularMatrix_secular_iff C c a z
    (hermitian_resolvent_det_ne_zero hC z
      (fun i => (hermitian_eigenvalue_le_norm hC i).trans_lt (hn.symm ▸ hz)))
    ((lt_of_le_of_lt (sq_nonneg ‖C‖) hz).ne')

omit [Fintype n] [DecidableEq n] in
theorem exceptionalVector_eq_zero_iff (c : n → ℝ) (a : ℝ) :
    exceptionalVector c a = 0 ↔ c = 0 ∧ a = 0 := by
  constructor
  · intro h
    constructor
    · funext i
      exact congrFun h (Sum.inl i)
    · exact congrFun h (Sum.inr ())
  · rintro ⟨rfl, rfl⟩
    ext i
    cases i <;> rfl

theorem cavitySecular_nonneg (C : Matrix n n ℝ) (c : n → ℝ) (a z : ℝ)
    (hz : ‖C‖ ^ 2 < z) : 0 ≤ cavitySecular C c a z := by
  rw [cavitySecular_eq_resolventForm C c a z hz]
  apply realResolventForm_nonneg (bulkGram_posSemidef C).isHermitian
  intro i
  exact (hermitian_eigenvalue_le_norm (bulkGram_posSemidef C).isHermitian i).trans_lt
    ((bulkGram_norm C).symm ▸ hz)

theorem cavitySecular_antitoneOn (C : Matrix n n ℝ) (c : n → ℝ) (a : ℝ) :
    AntitoneOn (cavitySecular C c a) (Set.Ioi (‖C‖ ^ 2)) := by
  intro z hz t ht hzt
  rw [cavitySecular_eq_resolventForm C c a z hz, cavitySecular_eq_resolventForm C c a t ht]
  apply realResolventForm_antitone (bulkGram_posSemidef C).isHermitian _ _ _ _ hzt
  intro i
  exact (hermitian_eigenvalue_le_norm (bulkGram_posSemidef C).isHermitian i).trans_lt
    ((bulkGram_norm C).symm ▸ hz)

theorem cavitySecular_strictAntiOn (C : Matrix n n ℝ) (c : n → ℝ) (a : ℝ)
    (hca : c ≠ 0 ∨ a ≠ 0) : StrictAntiOn (cavitySecular C c a) (Set.Ioi (‖C‖ ^ 2)) := by
  have hu : exceptionalVector c a ≠ 0 := by
    intro h
    obtain ⟨hc, ha⟩ := (exceptionalVector_eq_zero_iff c a).mp h
    rcases hca with hca | hca
    · exact hca hc
    · exact hca ha
  intro z hz t ht hzt
  rw [cavitySecular_eq_resolventForm C c a z hz, cavitySecular_eq_resolventForm C c a t ht]
  apply realResolventForm_strict_antitone (bulkGram_posSemidef C).isHermitian _ hu _ _ _ hzt
  intro i
  exact (hermitian_eigenvalue_le_norm (bulkGram_posSemidef C).isHermitian i).trans_lt
    ((bulkGram_norm C).symm ▸ hz)

theorem triangularMatrix_norm_le_iff (C : Matrix n n ℝ) (c : n → ℝ) (a z : ℝ)
    (hz : ‖C‖ ^ 2 < z) :
    ‖triangularMatrix C c a‖ ^ 2 ≤ z ↔ cavitySecular C c a z ≤ 1 := by
  have hn : ‖(triangularMatrix C c a)ᵀ * triangularMatrix C c a‖ =
      ‖triangularMatrix C c a‖ ^ 2 := by
    simpa [pow_two] using Matrix.l2_opNorm_conjTranspose_mul_self (triangularMatrix C c a)
  rw [← hn, triangularMatrix_gram, cavitySecular_eq_resolventForm C c a z hz]
  exact rankOne_norm_le_iff_resolvent_le (bulkGram_posSemidef C) _ z
    ((bulkGram_norm C).symm ▸ hz)

theorem triangularMatrix_norm_lt_iff (C : Matrix n n ℝ) (c : n → ℝ) (a z : ℝ)
    (hz : ‖C‖ ^ 2 < z) :
    ‖triangularMatrix C c a‖ ^ 2 < z ↔ cavitySecular C c a z < 1 := by
  have hn : ‖(triangularMatrix C c a)ᵀ * triangularMatrix C c a‖ =
      ‖triangularMatrix C c a‖ ^ 2 := by
    simpa [pow_two] using Matrix.l2_opNorm_conjTranspose_mul_self (triangularMatrix C c a)
  rw [← hn, triangularMatrix_gram, cavitySecular_eq_resolventForm C c a z hz]
  exact rankOne_norm_lt_iff_resolvent_lt (bulkGram_posSemidef C) _ z
    ((bulkGram_norm C).symm ▸ hz)

theorem triangularMatrix_norm_gap_iff (C : Matrix n n ℝ) (c : n → ℝ) (a z : ℝ)
    (hz : ‖C‖ ^ 2 < z) :
    z < ‖triangularMatrix C c a‖ ^ 2 ↔ 1 < cavitySecular C c a z := by
  simpa only [not_le] using not_congr (triangularMatrix_norm_le_iff C c a z hz)

theorem triangularMatrix_norm_sq_ge_bulk (C : Matrix n n ℝ) (c : n → ℝ) (a : ℝ) :
    ‖C‖ ^ 2 ≤ ‖triangularMatrix C c a‖ ^ 2 := by
  have hp : ((triangularMatrix C c a)ᵀ * triangularMatrix C c a - bulkGram C).PosSemidef := by
    rw [triangularMatrix_gram, add_sub_cancel_left]
    simpa using posSemidef_vecMulVec_self_star (exceptionalVector c a)
  have hn := posSemidef_norm_mono (bulkGram_posSemidef C) _ hp
  rw [bulkGram_norm] at hn
  have hg : ‖(triangularMatrix C c a)ᵀ * triangularMatrix C c a‖ =
      ‖triangularMatrix C c a‖ ^ 2 := by
    simpa [pow_two] using Matrix.l2_opNorm_conjTranspose_mul_self (triangularMatrix C c a)
  simpa [hg] using hn

theorem triangularMatrix_norm_ge_bulk (C : Matrix n n ℝ) (c : n → ℝ) (a : ℝ) :
    ‖C‖ ≤ ‖triangularMatrix C c a‖ := by
  have h := triangularMatrix_norm_sq_ge_bulk C c a
  nlinarith [norm_nonneg C, norm_nonneg (triangularMatrix C c a)]

theorem triangularMatrix_exterior_eigenvalue_indices_subsingleton
    (C : Matrix n n ℝ) (c : n → ℝ) (a : ℝ)
    (hG : ((triangularMatrix C c a)ᵀ * triangularMatrix C c a).IsHermitian) :
    Set.Subsingleton {i : n ⊕ Unit | ‖C‖ ^ 2 < hG.eigenvalues i} := by
  have hB : (bulkGram C + vecMulVec (exceptionalVector c a) (exceptionalVector c a)).IsHermitian :=
    triangularMatrix_gram C c a ▸ hG
  have h := rankOne_exterior_eigenvalue_indices_subsingleton (bulkGram_posSemidef C).isHermitian
    (exceptionalVector c a) hB
  simpa only [← triangularMatrix_gram, bulkGram_norm] using h

end FreeProbability.ReLU

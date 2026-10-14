import FreeProbability.OperatorValued.MatrixCauchyInfinity

/-! # Norm contraction prerequisite for normalized analytic matrix Dyson uniqueness

The uniqueness theorem here has an explicit small-norm condition. It does not
assert global pointwise uniqueness of all negative-imaginary-part solutions.
The matrix norm in this file is explicitly the submultiplicative row operator norm.
-/

noncomputable section
open scoped Classical Matrix.Norms.Operator
namespace FreeProbability

variable {I n : Type*} [Fintype I] [Fintype n] [DecidableEq n]

/-- Explicit covariance bound in the submultiplicative row operator matrix norm. -/
theorem matrixCovariance_norm_le (C : I → Matrix n n ℂ) (D : Matrix n n ℂ) :
    ‖matrixCovariance C D‖ ≤ (∑ i, ‖C i‖ ^ 2) * ‖D‖ := by
  rw [matrixCovariance_apply]
  calc
    _ ≤ ∑ i, ‖C i * D * C i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖C i‖ * ‖D‖ * ‖C i‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ = (∑ i, ‖C i‖ ^ 2) * ‖D‖ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- The exact ordered Dyson difference identity for any two matrix solutions. -/
theorem matrixDyson_difference (C : I → Matrix n n ℂ) (B M₁ M₂ : Matrix n n ℂ)
    (h₁ : (B - matrixCovariance C M₁) * M₁ = 1)
    (h₂ : (B - matrixCovariance C M₂) * M₂ = 1) :
    M₁ - M₂ = M₁ * matrixCovariance C (M₁ - M₂) * M₂ := by
  have hl₁ : M₁ * (B - matrixCovariance C M₁) = 1 := mul_eq_one_comm.mp h₁
  calc
    _ = M₁ * ((B - matrixCovariance C M₂) - (B - matrixCovariance C M₁)) * M₂ := by
      rw [mul_sub, sub_mul, mul_assoc M₁ (B - matrixCovariance C M₂) M₂, h₂,
        hl₁, mul_one, one_mul]
    _ = M₁ * matrixCovariance C (M₁ - M₂) * M₂ := by
      rw [map_sub]
      noncomm_ring

/-- Dyson solutions coincide whenever their two norms make the covariance
contraction factor strictly smaller than one. -/
theorem matrixDyson_unique_of_norm_small (C : I → Matrix n n ℂ) (B M₁ M₂ : Matrix n n ℂ)
    (h₁ : (B - matrixCovariance C M₁) * M₁ = 1)
    (h₂ : (B - matrixCovariance C M₂) * M₂ = 1)
    (hsmall : ‖M₁‖ * (∑ i, ‖C i‖ ^ 2) * ‖M₂‖ < 1) : M₁ = M₂ := by
  have hbound : ‖M₁ - M₂‖ ≤ (‖M₁‖ * (∑ i, ‖C i‖ ^ 2) * ‖M₂‖) * ‖M₁ - M₂‖ := by
    calc
      _ = ‖M₁ * matrixCovariance C (M₁ - M₂) * M₂‖ := congrArg norm (matrixDyson_difference C B M₁ M₂ h₁ h₂)
      _ ≤ ‖M₁‖ * ‖matrixCovariance C (M₁ - M₂)‖ * ‖M₂‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ ‖M₁‖ * ((∑ i, ‖C i‖ ^ 2) * ‖M₁ - M₂‖) * ‖M₂‖ := by
        gcongr
        exact matrixCovariance_norm_le C _
      _ = _ := by ring
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have hn := norm_nonneg (M₁ - M₂)
  nlinarith

end FreeProbability

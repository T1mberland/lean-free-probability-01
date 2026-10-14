import FreeProbability.OperatorValued.MatrixEdgeVariational

/-! # Positive-state lower bounds for the actual matrix spectral edge -/

noncomputable section
open scoped Classical ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix
namespace FreeProbability
variable {I n : Type*} [Fintype I] [Fintype n] [DecidableEq n] [Nonempty n]

omit [Nonempty n] in
/-- Weighted Cauchy--Schwarz for an arbitrary positive definite test matrix. -/
theorem matrixState_weighted_cauchySchwarz
    (φ : StarProbabilitySpace (Matrix n n ℂ)) (A Z : Matrix n n ℂ)
    (hA : A.IsHermitian) (hZ : Z.PosDef) :
    ‖φ.expectation A‖ ^ 2 ≤ (φ.expectation Z).re *
      (φ.expectation (A * Z⁻¹ * A)).re := by
  let S := CFC.sqrt Z
  have hSn : S.PosSemidef := (CFC.sqrt_nonneg Z).posSemidef
  have hSS : S * S = Z := CFC.sqrt_mul_sqrt_self Z hZ.posSemidef.nonneg
  have hSu : IsUnit S := isUnit_mul_self_iff.mp (hSS.symm ▸ hZ.isUnit)
  have hSi : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S ((Matrix.isUnit_iff_isUnit_det S).mp hSu)
  have hSr : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S ((Matrix.isUnit_iff_isUnit_det S).mp hSu)
  have hSii : S⁻¹ * S⁻¹ = Z⁻¹ := by
    symm
    apply Matrix.inv_eq_left_inv
    rw [← hSS, mul_assoc S⁻¹ S⁻¹ (S * S), ← mul_assoc S⁻¹ S S, hSi, one_mul, hSi]
  have hcross : star S * (S⁻¹ * A) = A := by
    change Sᴴ * (S⁻¹ * A) = A
    rw [hSn.isHermitian.eq, ← mul_assoc, hSr, one_mul]
  have hleft : star S * S = Z := by
    change Sᴴ * S = Z
    rw [hSn.isHermitian.eq, hSS]
  have hright : star (S⁻¹ * A) * (S⁻¹ * A) = A * Z⁻¹ * A := by
    change (S⁻¹ * A)ᴴ * (S⁻¹ * A) = A * Z⁻¹ * A
    rw [Matrix.conjTranspose_mul, hA.eq, hSn.isHermitian.inv.eq]
    simp only [mul_assoc, ← hSii]
  have h := φ.expectation_star_mul_norm_sq_le S (S⁻¹ * A)
  rw [hcross, hleft, hright] at h
  have hp : (A * Z⁻¹ * A).PosSemidef := by
    simpa only [hA.eq] using hZ.inv.posSemidef.conjTranspose_mul_mul_same A
  rw [← Complex.re_eq_norm.mpr (φ.expectation_nonneg hZ.posSemidef.nonneg),
    ← Complex.re_eq_norm.mpr (φ.expectation_nonneg hp.nonneg)] at h
  exact h

omit [Nonempty n] in
/-- A normalized positive state bounds each true variational test from below. -/
theorem matrixState_variational_value_lower
    (φ : StarProbabilitySpace (Matrix n n ℂ)) (C₀ : Matrix n n ℂ)
    (C : I → Matrix n n ℂ) (hC₀ : C₀.IsHermitian) (hC : ∀ i, (C i).IsHermitian)
    (Z : Matrix n n ℂ) (hZ : Z.PosDef) :
    (φ.expectation C₀).re + 2 * Real.sqrt (∑ i, ‖φ.expectation (C i)‖ ^ 2) ≤
      matrixMaxEigenvalue (C₀ + Z + matrixCovariance C Z⁻¹) := by
  let a := (φ.expectation Z).re
  let b := (φ.expectation (matrixCovariance C Z⁻¹)).re
  let d := ∑ i, ‖φ.expectation (C i)‖ ^ 2
  have ha : 0 ≤ a := (Complex.le_def.mp (φ.expectation_nonneg hZ.posSemidef.nonneg)).1
  have hb : 0 ≤ b := (Complex.le_def.mp (φ.expectation_nonneg
    (matrixCovariance_posSemidef C hC hZ.inv.posSemidef).nonneg)).1
  have hd : 0 ≤ d := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hbound : d ≤ a * b := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      matrixState_weighted_cauchySchwarz φ (C i) Z (hC i) hZ)
    simpa [a, b, d, matrixCovariance, map_sum, Finset.mul_sum] using h
  have hs := Real.sqrt_nonneg d
  have hs2 := Real.sq_sqrt hd
  have ham : 2 * Real.sqrt d ≤ a + b := by
    nlinarith [sq_nonneg (a - b)]
  let D := C₀ + Z + matrixCovariance C Z⁻¹
  have hD : D.IsHermitian := (hC₀.add hZ.isHermitian).add
    (matrixCovariance_isHermitian C hC _ hZ.isHermitian.inv)
  have hmax := φ.toPositiveLinearMap.monotone (le_algebraMap_realSpectralMaximum D hD)
  have hreal : (φ.expectation D).re ≤ matrixMaxEigenvalue D := by
    have hh := (Complex.le_def.mp hmax).1
    simpa [StarProbabilitySpace.toPositiveLinearMap_apply,
      IsScalarTower.algebraMap_apply ℝ ℂ (Matrix n n ℂ), matrixMaxEigenvalue] using hh
  have hex : (φ.expectation D).re = (φ.expectation C₀).re + a + b := by
    simp [D, a, b, map_add]
  rw [hex] at hreal
  change (φ.expectation C₀).re + 2 * Real.sqrt d ≤ matrixMaxEigenvalue D
  linarith

namespace Fock
/-- Every normalized positive scalar state gives a lower bound for the actual
spectral edge, for arbitrary Hermitian matrix coefficients. -/
theorem operatorMatrixPencilTopEdge_state_lower
    (φ : StarProbabilitySpace (Matrix n n ℂ)) (C₀ : Matrix n n ℂ)
    (C : I → Matrix n n ℂ) (hC₀ : C₀.IsHermitian) (hC : ∀ i, (C i).IsHermitian) :
    (φ.expectation C₀).re + 2 * Real.sqrt (∑ i, ‖φ.expectation (C i)‖ ^ 2) ≤
      operatorMatrixPencilTopEdge C₀ C := by
  rw [operatorMatrixPencilTopEdge_variational C₀ C hC₀ hC]
  apply le_csInf
  · exact ⟨matrixMaxEigenvalue (C₀ + 1 + matrixCovariance C 1⁻¹), 1, PosDef.one, rfl⟩
  · rintro r ⟨Z, hZ, rfl⟩
    exact matrixState_variational_value_lower φ C₀ C hC₀ hC Z hZ
end Fock
end FreeProbability

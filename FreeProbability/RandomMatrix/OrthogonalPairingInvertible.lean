import FreeProbability.RandomMatrix.OrthogonalPairingIndependence

/-! # Genuine ordinary pairing Gram positivity and stable inverse -/

noncomputable section
open scoped Classical
namespace FreeProbability.Orthogonal

/-- The exact ordinary-pairing matrix with its verified loop-count entries. -/
def ordinaryPairingGram (n : Type*) [Fintype n] (r : ℕ) :
    Matrix (OrdinaryPairing r) (OrdinaryPairing r) ℝ := fun p q =>
  (Fintype.card n : ℝ) ^ Fintype.card (Quotient (pairingSetoid p.out ⊔ pairingSetoid q.out))

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The closed loop-count matrix is the TRUE Gram matrix of the actual tensors. -/
theorem ordinaryPairingGram_eq_gram (r : ℕ) :
    ordinaryPairingGram n r = Matrix.gram ℝ (ordinaryPairingTensor (n := n) (r := r)) := by
  ext p q
  exact (pairingTensor_inner p.out q.out).symm

/-- Genuine positive semidefiniteness holds in ALL dimensions, even when
pairing tensors are dependent and an ordinary inverse need not exist. -/
theorem ordinaryPairingGram_posSemidef (r : ℕ) : (ordinaryPairingGram n r).PosSemidef := by
  rw [ordinaryPairingGram_eq_gram]
  exact Matrix.posSemidef_gram ℝ _

/-- Stable-dimension strict positivity follows from actual tensor independence. -/
theorem ordinaryPairingGram_posDef (r : ℕ) (hr : r ≤ Fintype.card n) :
    (ordinaryPairingGram n r).PosDef := by
  rw [ordinaryPairingGram_eq_gram]
  exact Matrix.posDef_gram_of_linearIndependent (ordinaryPairingTensor_linearIndependent r hr)

/-- Actual nonzero determinant, without assuming a formal Gram inverse. -/
theorem ordinaryPairingGram_det_ne_zero (r : ℕ) (hr : r ≤ Fintype.card n) :
    (ordinaryPairingGram n r).det ≠ 0 := by
  rw [ordinaryPairingGram_eq_gram]
  exact Matrix.det_gram_ne_zero_iff_linearIndependent.mpr (ordinaryPairingTensor_linearIndependent r hr)

/-- The genuine Gram matrix is a unit in stable dimension. -/
theorem ordinaryPairingGram_isUnit (r : ℕ) (hr : r ≤ Fintype.card n) :
    IsUnit (ordinaryPairingGram n r) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (ordinaryPairingGram_det_ne_zero r hr))

/-- Its literal matrix inverse is both a right and a left inverse. -/
theorem ordinaryPairingGram_inverse (r : ℕ) (hr : r ≤ Fintype.card n) :
    ordinaryPairingGram n r * (ordinaryPairingGram n r)⁻¹ = 1 ∧
      (ordinaryPairingGram n r)⁻¹ * ordinaryPairingGram n r = 1 := by
  have hd := isUnit_iff_ne_zero.mpr (ordinaryPairingGram_det_ne_zero r hr)
  exact ⟨Matrix.mul_nonsing_inv _ hd, Matrix.nonsing_inv_mul _ hd⟩
end FreeProbability.Orthogonal

import FreeProbability.OperatorValued.MatrixSquareCertificate

/-! # Actual real spectral maxima and largest eigenvalues -/

noncomputable section
open scoped Classical MatrixOrder Matrix.Norms.L2Operator
open Matrix
namespace FreeProbability

/-- The supremum of the actual real spectrum in a C-star algebra. -/
def realSpectralMaximum {A : Type*} [CStarAlgebra A] (a : A) : ℝ := sSup (spectrum ℝ a)

section General
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]

omit [PartialOrder A] [StarOrderedRing A] in
/-- A self-adjoint element's actual spectral maximum belongs to its spectrum. -/
theorem realSpectralMaximum_mem (a : A) (ha : IsSelfAdjoint a) :
    realSpectralMaximum a ∈ spectrum ℝ a := by
  have hc : IsCompact (spectrum ℝ a) := ContinuousFunctionalCalculus.isCompact_spectrum a
  exact hc.isClosed.csSup_mem (ContinuousFunctionalCalculus.spectrum_nonempty a ha) hc.bddAbove

omit [PartialOrder A] [StarOrderedRing A] [Nontrivial A] in
/-- Every actual real spectral value is bounded by the spectral maximum. -/
theorem le_realSpectralMaximum (a : A) (x : ℝ) (hx : x ∈ spectrum ℝ a) :
    x ≤ realSpectralMaximum a := by
  have hc : IsCompact (spectrum ℝ a) := ContinuousFunctionalCalculus.isCompact_spectrum a
  exact le_csSup hc.bddAbove hx

omit [PartialOrder A] [StarOrderedRing A] in
/-- The full right-exterior condition is precisely being above the actual maximum. -/
theorem realSpectralMaximum_lt_iff (a : A) (ha : IsSelfAdjoint a) (x : ℝ) :
    realSpectralMaximum a < x ↔ ∀ t ∈ spectrum ℝ a, t < x := by
  constructor
  · intro h t ht
    exact (le_realSpectralMaximum a t ht).trans_lt h
  · intro h
    exact h _ (realSpectralMaximum_mem a ha)

omit [Nontrivial A] in
/-- Functional calculus bounds the actual self-adjoint operator by its maximum. -/
theorem le_algebraMap_realSpectralMaximum (a : A) (ha : IsSelfAdjoint a) :
    a ≤ algebraMap ℝ A (realSpectralMaximum a) :=
  le_algebraMap_of_spectrum_le (fun x hx => le_realSpectralMaximum a x hx) ha

/-- Operator order bounds imply upper bounds on the actual spectral maximum. -/
theorem realSpectralMaximum_le_of_le_algebraMap (a : A) (ha : IsSelfAdjoint a) (x : ℝ)
    (h : a ≤ algebraMap ℝ A x) : realSpectralMaximum a ≤ x := by
  apply csSup_le (ContinuousFunctionalCalculus.spectrum_nonempty a ha)
  exact (le_algebraMap_iff_spectrum_le ha).mp h

end General

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- Largest real spectral value of a finite complex matrix; for Hermitian
matrices this is the actual largest eigenvalue. -/
def matrixMaxEigenvalue (D : Matrix n n ℂ) : ℝ := realSpectralMaximum D

omit [Nonempty n] in
theorem matrixMaxEigenvalue_eq_sup_eigenvalues (D : Matrix n n ℂ) (hD : D.IsHermitian) :
    matrixMaxEigenvalue D = sSup (Set.range hD.eigenvalues) := by
  unfold matrixMaxEigenvalue realSpectralMaximum
  rw [hD.spectrum_real_eq_range_eigenvalues]

/-- The defined maximum is itself an eigenvalue of the Hermitian matrix. -/
theorem matrixMaxEigenvalue_is_eigenvalue (D : Matrix n n ℂ) (hD : D.IsHermitian) :
    ∃ i, hD.eigenvalues i = matrixMaxEigenvalue D := by
  have hm := realSpectralMaximum_mem D hD
  rw [hD.spectrum_real_eq_range_eigenvalues] at hm
  exact hm

omit [Nonempty n] in
/-- Every eigenvalue lies below the actual matrix maximum. -/
theorem eigenvalue_le_matrixMaxEigenvalue (D : Matrix n n ℂ) (hD : D.IsHermitian) (i : n) :
    hD.eigenvalues i ≤ matrixMaxEigenvalue D :=
  le_realSpectralMaximum D _ (hD.eigenvalues_mem_spectrum_real i)

/-- A scalar matrix has its actual scalar as largest eigenvalue. -/
@[simp] theorem matrixMaxEigenvalue_scalar (x : ℝ) :
    matrixMaxEigenvalue ((x : ℂ) • (1 : Matrix n n ℂ)) = x := by
  unfold matrixMaxEigenvalue realSpectralMaximum
  have hc : (x : ℂ) • (1 : Matrix n n ℂ) = algebraMap ℝ (Matrix n n ℂ) x := by
    rw [Algebra.algebraMap_eq_smul_one, Complex.coe_smul]
  rw [hc, spectrum.scalar_eq, csSup_singleton]

end FreeProbability

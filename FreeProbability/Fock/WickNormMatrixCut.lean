import FreeProbability.Fock.WickNormCreatorFamily
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Hilbert-Schmidt bound for each actual normal-order matrix cut

Orthogonal prefix creator ranges and the complete annihilator Bessel bound give
an operator norm bound by the square-sum of the matrix of color coefficients.
The color index sets are arbitrary; only the coefficient sums are finite.
-/

noncomputable section
open scoped Classical InnerProductSpace

namespace FreeProbability.Fock

variable {I : Type*}

/-- Finite vector Cauchy-Schwarz for complex coefficients and arbitrary actual Fock vectors. -/
theorem norm_sum_smul_sq_le {J : Type*} (s : Finset J) (c : J → ℂ) (f : J → WordSpace I) :
    ‖∑ j ∈ s, c j • f j‖ ^ 2 ≤ (∑ j ∈ s, ‖c j‖ ^ 2) * ∑ j ∈ s, ‖f j‖ ^ 2 := by
  have hn : ‖∑ j ∈ s, c j • f j‖ ≤ ∑ j ∈ s, ‖c j‖ * ‖f j‖ := by
    simpa only [norm_smul] using norm_sum_le s (fun j => c j • f j)
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq s (fun j => ‖c j‖) (fun j => ‖f j‖))

/-- An actual bounded normal-order cut with a finite matrix of prefix/suffix coefficients. -/
def wickCreatorMatrixCut (p q : ℕ) (s : Finset (Fin p → I)) (t : Finset (Fin q → I))
    (a : (Fin p → I) → (Fin q → I) → ℂ) : WordSpace I →L[ℂ] WordSpace I :=
  ∑ u ∈ s, ∑ v ∈ t, a u v •
    (creationWord (List.ofFn u) * annihilationWord (List.ofFn v).reverse)

/-- The matrix cut acts by orthogonal prefix creators applied to its coefficient rows. -/
theorem wickCreatorMatrixCut_apply (p q : ℕ) (s : Finset (Fin p → I)) (t : Finset (Fin q → I))
    (a : (Fin p → I) → (Fin q → I) → ℂ) (f : WordSpace I) :
    wickCreatorMatrixCut p q s t a f =
      ∑ u ∈ s, creationWord (List.ofFn u)
        (∑ v ∈ t, a u v • annihilationWord (List.ofFn v).reverse f) := by
  simp only [wickCreatorMatrixCut, sum_apply, smul_apply,
    mul_apply_eq_comp, map_sum, map_smul]

/-- Actual operator action satisfies the square-sum coefficient bound for every Fock vector. -/
theorem norm_wickCreatorMatrixCut_apply_sq_le
    (p q : ℕ) (s : Finset (Fin p → I)) (t : Finset (Fin q → I))
    (a : (Fin p → I) → (Fin q → I) → ℂ) (f : WordSpace I) :
    ‖wickCreatorMatrixCut p q s t a f‖ ^ 2 ≤
      (∑ u ∈ s, ∑ v ∈ t, ‖a u v‖ ^ 2) * ‖f‖ ^ 2 := by
  rw [wickCreatorMatrixCut_apply]
  have ho := (orthogonal_creationWordFamily (I := I) p).norm_sum
    (fun u => ∑ v ∈ t, a u v • annihilationWord (List.ofFn v).reverse f) s
  change ‖∑ u ∈ s, creationWord (List.ofFn u)
    (∑ v ∈ t, a u v • annihilationWord (List.ofFn v).reverse f)‖ ^ 2 = _ at ho
  rw [ho]
  calc
    _ ≤ ∑ u ∈ s, (∑ v ∈ t, ‖a u v‖ ^ 2) * ‖f‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro u hu
      exact (norm_sum_smul_sq_le t (a u) _).trans
        (mul_le_mul_of_nonneg_left (sum_norm_annihilationWord_sq_le q t f)
          (Finset.sum_nonneg (fun v hv => sq_nonneg _)))
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- Each normal-order matrix cut has actual operator norm at most its Hilbert-Schmidt coefficient norm. -/
theorem norm_wickCreatorMatrixCut_le
    (p q : ℕ) (s : Finset (Fin p → I)) (t : Finset (Fin q → I))
    (a : (Fin p → I) → (Fin q → I) → ℂ) :
    ‖wickCreatorMatrixCut p q s t a‖ ≤ Real.sqrt (∑ u ∈ s, ∑ v ∈ t, ‖a u v‖ ^ 2) := by
  refine ContinuousLinearMap.opNorm_le_bound (wickCreatorMatrixCut p q s t a) (Real.sqrt_nonneg _) ?_
  intro f
  have hc : 0 ≤ ∑ u ∈ s, ∑ v ∈ t, ‖a u v‖ ^ 2 :=
    Finset.sum_nonneg (fun u _ => Finset.sum_nonneg (fun v _ => sq_nonneg _))
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  simpa only [mul_pow, Real.sq_sqrt hc] using
    norm_wickCreatorMatrixCut_apply_sq_le p q s t a f

end FreeProbability.Fock

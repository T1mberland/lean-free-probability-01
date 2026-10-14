import FreeProbability.Fock.WickNormHomogeneousCut
import FreeProbability.Fock.LengthDecomposition

/-!
# Actual homogeneous Wick Haagerup inequality

For every degree and every finite family of color-word coefficients, the actual
bounded Wick polynomial has operator norm at most degree plus one times its
actual vacuum Hilbert norm. No finiteness or countability of the color set is
assumed. The proof preserves the square-sum of all coefficients at every cut.
-/

noncomputable section
open scoped Classical InnerProductSpace

namespace FreeProbability.Fock

variable {I : Type*}

/-- An actual finite homogeneous Wick polynomial of fixed degree. -/
def homogeneousWick (n : ℕ) (c : (Fin n → I) →₀ ℂ) : WordSpace I →L[ℂ] WordSpace I :=
  c.sum fun a z => z • wick (List.ofFn a)

/-- The normal-order expansion for a fixed-degree tuple uses the exact degree-sized cut set. -/
theorem wick_ofFn_normal_order (n : ℕ) (a : Fin n → I) :
    wick (List.ofFn a) = ∑ k : Fin (n + 1),
      creationWord ((List.ofFn a).take k.val) * annihilationWord ((List.ofFn a).drop k.val) := by
  rw [wick_normal_order_expansion]
  apply Fintype.sum_equiv (finCongr (show (List.ofFn a).length + 1 = n + 1 by simp))
  intro k
  rfl

/-- Each arbitrary degree cut has the actual original coefficient Hilbert norm bound. -/
theorem norm_homogeneousWick_degree_cut_le (n : ℕ) (c : (Fin n → I) →₀ ℂ)
    (p q : ℕ) (hpq : p + q = n) :
    ‖c.sum (fun a z => z •
      (creationWord ((List.ofFn a).take p) * annihilationWord ((List.ofFn a).drop p)))‖ ≤
        Real.sqrt (c.sum fun _ z => ‖z‖ ^ 2) := by
  subst n
  exact norm_homogeneousWickCut_le p q c

/-- Actual finite homogeneous Wick sums are the sum of exactly `n+1` norm-controlled cuts. -/
theorem homogeneousWick_normal_order (n : ℕ) (c : (Fin n → I) →₀ ℂ) :
    homogeneousWick n c = ∑ k : Fin (n + 1), c.sum (fun a z => z •
      (creationWord ((List.ofFn a).take k.val) * annihilationWord ((List.ofFn a).drop k.val))) := by
  unfold homogeneousWick
  simp_rw [wick_ofFn_normal_order]
  simp only [Finsupp.sum, Finset.smul_sum]
  rw [Finset.sum_comm]

/-- Actual operator norm is bounded by degree plus one times the original coefficient square-sum norm. -/
theorem norm_homogeneousWick_le (n : ℕ) (c : (Fin n → I) →₀ ℂ) :
    ‖homogeneousWick n c‖ ≤ ((n : ℝ) + 1) * Real.sqrt (c.sum fun _ z => ‖z‖ ^ 2) := by
  rw [homogeneousWick_normal_order]
  calc
    _ ≤ ∑ k : Fin (n + 1), ‖c.sum (fun a z => z •
      (creationWord ((List.ofFn a).take k.val) * annihilationWord ((List.ofFn a).drop k.val)))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _ : Fin (n + 1), Real.sqrt (c.sum fun _ z => ‖z‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro k hk
      exact norm_homogeneousWick_degree_cut_le n c k.val (n - k.val) (by omega)
    _ = _ := by simp

/-- The actual homogeneous Wick vacuum vector has precisely the original word coefficients. -/
@[simp] theorem homogeneousWick_vacuum (n : ℕ) (c : (Fin n → I) →₀ ℂ) :
    homogeneousWick n c (vacuum : WordSpace I) = c.sum (fun a z => z • word (List.ofFn a)) := by
  simp only [homogeneousWick, Finsupp.sum, sum_apply, smul_apply, wick_vacuum]

/-- The actual vacuum squared Hilbert norm is exactly the coefficient square-sum. -/
theorem norm_homogeneousWick_vacuum_sq (n : ℕ) (c : (Fin n → I) →₀ ℂ) :
    ‖homogeneousWick n c (vacuum : WordSpace I)‖ ^ 2 = c.sum (fun _ z => ‖z‖ ^ 2) := by
  have h := (orthonormal_fixedLength (I := I) n).orthogonalFamily.norm_sum
    (fun a => c a) c.support
  simpa only [homogeneousWick_vacuum, Finsupp.sum, LinearIsometry.toSpanSingleton_apply] using h

/-- The full homogeneous polynomial Haagerup inequality in the actual Fock operator/vacuum norms. -/
theorem norm_homogeneousWick_le_degree_mul_vacuumNorm (n : ℕ) (c : (Fin n → I) →₀ ℂ) :
    ‖homogeneousWick n c‖ ≤ ((n : ℝ) + 1) * ‖homogeneousWick n c (vacuum : WordSpace I)‖ := by
  have h := norm_homogeneousWick_le n c
  rw [← norm_homogeneousWick_vacuum_sq, Real.sqrt_sq (norm_nonneg _)] at h
  exact h

end FreeProbability.Fock

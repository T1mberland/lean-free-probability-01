import FreeProbability.Fock.WickSuffixGramMarginal
import Mathlib.Analysis.InnerProductSpace.Positive

/-! # Genuine finite Hilbert-operator Cauchy--Schwarz Gram inequality -/
noncomputable section
open scoped Classical BigOperators InnerProductSpace ComplexOrder
namespace FreeProbability.Fock
variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [InnerProductSpace ℂ E] [CompleteSpace E] in
/-- Finite vector Cauchy--Schwarz, without enumerating the Hilbert space. -/
theorem norm_finset_sum_sq_le (S : Finset ι) (f : ι → E) :
    ‖∑ i ∈ S, f i‖ ^ 2 ≤ (S.card : ℝ) * ∑ i ∈ S, ‖f i‖ ^ 2 := by
  calc
    _ ≤ (∑ i ∈ S, ‖f i‖) ^ 2 := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ _ := by
      simpa using Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun i => ‖f i‖)

/-- Genuine full bounded-operator order Cauchy--Schwarz, tested on all Hilbert vectors. -/
theorem finiteOperatorGram_le (S : Finset ι) (A : ι → E →L[ℂ] E) :
    (∑ i ∈ S, A i) * star (∑ i ∈ S, A i) ≤
      (S.card : ℂ) • ∑ i ∈ S, A i * star (A i) := by
  rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_iff_complex]
  intro f
  have hi (T : E →L[ℂ] E) :
      inner ℂ ((T * star T) f) f = (‖star T f‖ ^ 2 : ℝ) := by
    rw [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
      ← ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    norm_cast
  have he : inner ℂ
      (((S.card : ℂ) • ∑ i ∈ S, A i * star (A i) -
        (∑ i ∈ S, A i) * star (∑ i ∈ S, A i)) f) f =
      ((S.card : ℝ) * (∑ i ∈ S, ‖star (A i) f‖ ^ 2) -
        ‖∑ i ∈ S, star (A i) f‖ ^ 2 : ℝ) := by
    rw [sub_apply, inner_sub_left, smul_apply, inner_smul_left, hi,
      sum_apply, sum_inner]
    simp_rw [hi]
    simp only [star_sum, sum_apply, map_natCast]
    push_cast
    rfl

  rw [he]
  let q : ℝ := (S.card : ℝ) * (∑ i ∈ S, ‖star (A i) f‖ ^ 2) -
    ‖∑ i ∈ S, star (A i) f‖ ^ 2
  constructor
  · change (Complex.re (Complex.ofReal q) : ℂ) = Complex.ofReal q
    rw [Complex.ofReal_re]
  · change 0 ≤ Complex.re (Complex.ofReal _)
    rw [Complex.ofReal_re]
    exact sub_nonneg.mpr (norm_finset_sum_sq_le S (fun i => star (A i) f))

/-- The full canonical finite-matrix operator Cauchy--Schwarz inequality. -/
theorem finiteMatrixOperatorGram_le {ν : Type*} [Fintype ν] (S : Finset ι)
    (A : ι → CStarMatrix ν ν (E →L[ℂ] E)) :
    (∑ i ∈ S, A i) * star (∑ i ∈ S, A i) ≤
      (S.card : ℂ) • ∑ i ∈ S, A i * star (A i) := by
  let Φ := hilbertMatrixStarAlgEquiv (N := ν) (E := E)
  apply (NonUnitalStarAlgHom.map_le_map_iff Φ Φ.injective).mp
  simp only [map_mul, map_star, map_sum, map_smul]
  exact finiteOperatorGram_le S (fun i => Φ (A i))

end FreeProbability.Fock

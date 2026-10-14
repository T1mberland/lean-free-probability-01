import FreeProbability.Fock.WordSpace
import FreeProbability.Algebraic.StarProbabilitySpace

/-!
# Positive vacuum state and elementary semicircular bounds

This is a positive normalized state on all bounded word-space operators. It is
not asserted faithful or tracial there. The restriction to the generated
semicircular algebra, including its faithfulness and traciality, remains a
separate mathematical obligation.
-/

noncomputable section
open scoped ComplexOrder InnerProductSpace Classical

namespace FreeProbability.Fock

variable {I : Type*}

/-- Vacuum evaluation as a linear functional. -/
def vacuumLinear : (WordSpace I →L[ℂ] WordSpace I) →ₗ[ℂ] ℂ where
  toFun := vacuumExpectation
  map_add' T U := by simp [vacuumExpectation, inner_add_right]
  map_smul' c T := by simp [vacuumExpectation, inner_smul_right]

@[simp] theorem vacuumExpectation_one :
    vacuumExpectation (1 : WordSpace I →L[ℂ] WordSpace I) = 1 := by
  simp [vacuumExpectation, vacuum]

@[simp] theorem vacuumExpectation_star (T : WordSpace I →L[ℂ] WordSpace I) :
    vacuumExpectation (star T) = star (vacuumExpectation T) := by
  simp only [vacuumExpectation, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  exact (inner_conj_symm (𝕜 := ℂ) (T vacuum) (vacuum : WordSpace I)).symm

/-- Positivity is the actual squared norm of the vacuum image. -/
theorem vacuumExpectation_star_mul_self (T : WordSpace I →L[ℂ] WordSpace I) :
    vacuumExpectation (star T * T) = (‖T vacuum‖ : ℂ) ^ 2 := by
  simp only [vacuumExpectation, mul_apply_eq_comp,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K]
  rfl

/-- A genuine positive normalized noncommutative probability space. -/
def vacuumState (I : Type*) : StarProbabilitySpace (WordSpace I →L[ℂ] WordSpace I) where
  expectation := vacuumLinear
  map_one := vacuumExpectation_one
  map_star := vacuumExpectation_star
  positive T := by
    change 0 ≤ vacuumExpectation (star T * T)
    rw [vacuumExpectation_star_mul_self]
    rw [← Complex.ofReal_pow]
    exact Complex.zero_le_real.mpr (sq_nonneg _)

@[simp] theorem vacuumState_expectation (T : WordSpace I →L[ℂ] WordSpace I) :
    (vacuumState I).expectation T = vacuumExpectation T := rfl

/-- The vacuum state is continuous with operator-norm bound one. -/
theorem norm_vacuumExpectation_le (T : WordSpace I →L[ℂ] WordSpace I) :
    ‖vacuumExpectation T‖ ≤ ‖T‖ := by
  calc
    ‖vacuumExpectation T‖ ≤ ‖(vacuum : WordSpace I)‖ * ‖T vacuum‖ := norm_inner_le_norm _ _
    _ ≤ ‖T‖ := by simpa using T.le_opNorm (vacuum : WordSpace I)

@[simp] theorem norm_creation (i : I) : ‖creation i‖ = 1 := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0 : ℝ) ≤ 1)
    intro f
    simp
  · have h := (creation i).le_opNorm (vacuum : WordSpace I)
    simpa using h

@[simp] theorem norm_annihilation (i : I) : ‖annihilation i‖ = 1 := by
  change ‖star (creation i)‖ = 1
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint.norm_map, norm_creation]

/-- Elementary upper bound; the matching lower bound two remains to be proved. -/
theorem norm_semicircular_le_two (i : I) : ‖semicircular i‖ ≤ 2 := by
  calc
    ‖semicircular i‖ ≤ ‖creation i‖ + ‖annihilation i‖ := norm_add_le _ _
    _ = 2 := by simp only [norm_creation, norm_annihilation]; norm_num

/-- Self-adjointness in the star algebra of bounded operators. -/
theorem isSelfAdjoint_semicircular (i : I) : IsSelfAdjoint (semicircular i) :=
  ContinuousLinearMap.isSelfAdjoint_iff'.mpr (adjoint_semicircular i)

/-- Variance one in the actual positive vacuum probability space. -/
@[simp] theorem vacuumState_semicircular_sq (i : I) :
    (vacuumState I).expectation (semicircular i ^ 2) = 1 := by
  change vacuumExpectation ((semicircular i).comp (semicircular i)) = 1
  simpa using vacuumExpectation_semicircular_comp i i

end FreeProbability.Fock

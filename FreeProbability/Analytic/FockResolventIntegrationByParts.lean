import FreeProbability.Fock.WordIntegrationByParts
import FreeProbability.Analytic.CauchyHalfPlane

/-!
# Actual semicircular resolvent integration by parts

The vacuum boundary commutator differentiates inverses on their exact resolvent
set. No formal-series identity or convergence assumption substitutes for an
actual operator inverse.
-/

noncomputable section
open scoped Classical
namespace FreeProbability

/-- The inverse commutator identity preserves noncommutative order. -/
theorem commutator_inverse_unit {A : Type*} [Ring A] (C : A) (u : Aˣ) :
    C * (↑u⁻¹ : A) - (↑u⁻¹ : A) * C =
      (↑u⁻¹ : A) * ((u : A) * C - C * (u : A)) * (↑u⁻¹ : A) := by
  calc
    _ = ((↑u⁻¹ : A) * (u : A)) * C * (↑u⁻¹ : A) -
        (↑u⁻¹ : A) * C * ((u : A) * (↑u⁻¹ : A)) := by simp
    _ = _ := by noncomm_ring

namespace Fock
variable {I : Type*}

/-- Rank-one resolvent derivative at every actual resolvent point. -/
theorem rightAnnihilation_resolvent_commutator (i j : I) (z : ℂ)
    (hz : z ∈ resolventSet ℂ (semicircular j)) :
    rightAnnihilation i * resolvent (semicircular j) z -
      resolvent (semicircular j) z * rightAnnihilation i =
      if i = j then resolvent (semicircular j) z * vacuumProjection *
        resolvent (semicircular j) z else 0 := by
  have h := commutator_inverse_unit (rightAnnihilation i) hz.unit
  rw [← spectrum.resolvent_eq hz, hz.unit_spec] at h
  have hb : (algebraMap ℂ (WordSpace I →L[ℂ] WordSpace I) z - semicircular j) *
      rightAnnihilation i - rightAnnihilation i *
        (algebraMap ℂ (WordSpace I →L[ℂ] WordSpace I) z - semicircular j) =
      rightAnnihilation i * semicircular j - semicircular j * rightAnnihilation i := by
    simp only [sub_mul, mul_sub, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    abel
  rw [hb, rightAnnihilation_semicircular_commutator] at h
  by_cases hij : i = j <;> simpa [hij] using h

/-- Free resolvent IBP on the entire actual resolvent set. -/
theorem vacuumExpectation_semicircular_mul_resolvent (i j : I) (z : ℂ)
    (hz : z ∈ resolventSet ℂ (semicircular j)) :
    vacuumExpectation (semicircular i * resolvent (semicircular j) z) =
      if i = j then vacuumExpectation (resolvent (semicircular j) z) ^ 2 else 0 := by
  rw [← vacuumExpectation_rightAnnihilation_commutator,
    rightAnnihilation_resolvent_commutator i j z hz]
  by_cases hij : i = j
  · simp only [hij, ite_true]
    rw [vacuumExpectation_mul_vacuumProjection_mul, pow_two]
  · simp [hij, vacuumExpectation]

/-- The actual semicircular resolvent expectation satisfies its quadratic equation
at every invertibility point, with no formal-series restriction. -/
theorem vacuumExpectation_resolvent_quadratic (j : I) (z : ℂ)
    (hz : z ∈ resolventSet ℂ (semicircular j)) :
    vacuumExpectation (resolvent (semicircular j) z) ^ 2 -
      z * vacuumExpectation (resolvent (semicircular j) z) + 1 = 0 := by
  have hr : (algebraMap ℂ (WordSpace I →L[ℂ] WordSpace I) z - semicircular j) *
      resolvent (semicircular j) z = 1 :=
    Ring.mul_inverse_cancel _ hz
  have he := congrArg (vacuumState I).expectation hr
  simp only [sub_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
    one_mul, map_sub, map_smul, smul_eq_mul, (vacuumState I).map_one] at he
  change z * vacuumExpectation (resolvent (semicircular j) z) -
    vacuumExpectation (semicircular j * resolvent (semicircular j) z) = 1 at he
  rw [vacuumExpectation_semicircular_mul_resolvent j j z hz, ite_eq_left rfl] at he
  linear_combination -he

/-- Every nonreal argument lies in the actual semicircular resolvent domain. -/
theorem vacuumExpectation_semicircular_mul_resolvent_nonreal (i j : I) (z : ℂ)
    (hz : z.im ≠ 0) :
    vacuumExpectation (semicircular i * resolvent (semicircular j) z) =
      if i = j then vacuumExpectation (resolvent (semicircular j) z) ^ 2 else 0 :=
  vacuumExpectation_semicircular_mul_resolvent i j z
    (StarProbabilitySpace.selfAdjoint_mem_resolventSet_of_im_ne_zero
      (semicircular j) (isSelfAdjoint_semicircular j) z hz)

end Fock
end FreeProbability

import FreeProbability.Analytic.FockResolventIntegrationByParts
import FreeProbability.Semicircular.SpectralIdentification

/-! # Actual generated-algebra resolvents and the semicircular physical branch -/

noncomputable section
open scoped Classical
namespace FreeProbability

/-- An algebra homomorphism preserves the actual inverse at invertible inputs. -/
theorem algHom_map_ringInverse_of_isUnit {𝕜 A B : Type*} [CommRing 𝕜]
    [Ring A] [Ring B] [Algebra 𝕜 A] [Algebra 𝕜 B]
    (f : A →ₐ[𝕜] B) {a : A} (ha : IsUnit a) :
    f (Ring.inverse a) = Ring.inverse (f a) := by
  rcases ha with ⟨u, rfl⟩
  rw [Ring.inverse_unit]
  simpa using (Ring.inverse_unit (Units.map f.toMonoidHom u)).symm

/-- A quadratic with constant coefficient one has at most one root in the
strict lower half-plane. This selects the actual physical Cauchy branch. -/
theorem semicircular_quadratic_lower_root_unique {z x y : ℂ}
    (hx : x ^ 2 - z * x + 1 = 0) (hy : y ^ 2 - z * y + 1 = 0)
    (hxi : x.im < 0) (hyi : y.im < 0) : x = y := by
  have hf : (x - y) * (x + y - z) = 0 := by linear_combination hx - hy
  rcases mul_eq_zero.mp hf with hxy | hs
  · exact sub_eq_zero.mp hxy
  · have hz : z = x + y := (sub_eq_zero.mp hs).symm
    have hp : x * y = 1 := by rw [hz] at hx; linear_combination -hx
    have hn : x ≠ 0 := by intro h; simp [h] at hp
    have he : y = x⁻¹ := by apply mul_left_cancel₀ hn; simp [hp, hn]
    have hi : 0 < y.im := by
      rw [he, Complex.inv_im]
      exact div_pos (neg_pos.mpr hxi) (Complex.normSq_pos.mpr hn)
    linarith

namespace Fock
variable {I : Type*}

local instance : PartialOrder (closedSemicircularAlgebra I) := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing (closedSemicircularAlgebra I) := CStarAlgebra.spectralOrderedRing _

/-- Spectral permanence identifies the entire intrinsic and ambient domains. -/
theorem closedSemicircular_mem_resolventSet_iff (i : I) (z : ℂ) :
    z ∈ resolventSet ℂ (closedSemicircular i) ↔
      z ∈ resolventSet ℂ (semicircular i) :=
  not_iff_not.mp (StarSubalgebra.mem_spectrum_iff (closedSemicircularAlgebra I)
    (a := closedSemicircular i) (z := z))

/-- The actual intrinsic resolvent maps to the actual bounded-operator inverse. -/
theorem coe_resolvent_closedSemicircular (i : I) (z : ℂ)
    (hz : z ∈ resolventSet ℂ (closedSemicircular i)) :
    (closedSemicircularAlgebra I).subtype.toAlgHom (resolvent (closedSemicircular i) z) =
      resolvent (semicircular i) z := by
  change (closedSemicircularAlgebra I).subtype.toAlgHom
    (Ring.inverse (algebraMap ℂ _ z - closedSemicircular i)) = _
  have h := algHom_map_ringInverse_of_isUnit
    (closedSemicircularAlgebra I).subtype.toAlgHom hz
  simpa [map_sub, resolvent, closedSemicircular, StarSubalgebra.subtype_apply] using h

/-- Resolvent IBP holds in the literal faithful tracial generated C-star state. -/
theorem closedGeneratedVacuumState_semicircular_mul_resolvent (i j : I) (z : ℂ)
    (hz : z ∈ resolventSet ℂ (closedSemicircular j)) :
    (closedGeneratedVacuumState I).expectation
      (closedSemicircular i * resolvent (closedSemicircular j) z) =
      if i = j then (closedGeneratedVacuumState I).cauchyTransform
        (closedSemicircular j) z ^ 2 else 0 := by
  change vacuumExpectation ((closedSemicircularAlgebra I).subtype.toAlgHom
    (closedSemicircular i * resolvent (closedSemicircular j) z)) =
    if i = j then vacuumExpectation ((closedSemicircularAlgebra I).subtype.toAlgHom
      (resolvent (closedSemicircular j) z)) ^ 2 else 0
  rw [map_mul, coe_resolvent_closedSemicircular j z hz]
  change vacuumExpectation (semicircular i * resolvent (semicircular j) z) = _
  exact vacuumExpectation_semicircular_mul_resolvent i j z
    ((closedSemicircular_mem_resolventSet_iff j z).mp hz)

/-- The actual generated-state Cauchy transform satisfies the quadratic on its
whole resolvent domain, including real exterior points. -/
theorem closedSemicircular_cauchyTransform_quadratic (i : I) (z : ℂ)
    (hz : z ∈ resolventSet ℂ (closedSemicircular i)) :
    (closedGeneratedVacuumState I).cauchyTransform (closedSemicircular i) z ^ 2 -
      z * (closedGeneratedVacuumState I).cauchyTransform (closedSemicircular i) z + 1 = 0 := by
  change vacuumExpectation ((closedSemicircularAlgebra I).subtype.toAlgHom
    (resolvent (closedSemicircular i) z)) ^ 2 -
    z * vacuumExpectation ((closedSemicircularAlgebra I).subtype.toAlgHom
      (resolvent (closedSemicircular i) z)) + 1 = 0
  rw [coe_resolvent_closedSemicircular i z hz]
  exact vacuumExpectation_resolvent_quadratic i z
    ((closedSemicircular_mem_resolventSet_iff i z).mp hz)

/-- The actual Cauchy transform is the unique quadratic root with negative
imaginary part throughout the upper half-plane. -/
theorem closedSemicircular_cauchyTransform_physical_branch (i : I) (z : ℂ)
    (hz : 0 < z.im) (w : ℂ) (hw : w ^ 2 - z * w + 1 = 0) (hwi : w.im < 0) :
    w = (closedGeneratedVacuumState I).cauchyTransform (closedSemicircular i) z := by
  apply semicircular_quadratic_lower_root_unique hw
    (closedSemicircular_cauchyTransform_quadratic i z
      (StarProbabilitySpace.selfAdjoint_mem_resolventSet_of_im_ne_zero
        _ (isSelfAdjoint_closedSemicircular i) z hz.ne')) hwi
  exact (closedGeneratedVacuumState I).cauchyTransform_im_neg
    _ (isSelfAdjoint_closedSemicircular i) z hz

end Fock
end FreeProbability

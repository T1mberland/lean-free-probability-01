import FreeProbability.Fock.SecondQuantizationFunctor

/-!
# Conjugation of fields by second quantization

These are identities between genuine bounded operators. They express covariance
under an arbitrary complex Hilbert unitary, without identifying the original
chosen real generated algebra with its rotated image.
-/

noncomputable section
open scoped InnerProductSpace

namespace FreeProbability.Fock
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The self-adjoint field h ↦ creation(h) + annihilation(h) is unitarily covariant. -/
theorem secondQuantization_conj_field (U : H ≃ₗᵢ[ℂ] H) (h : H) :
    (secondQuantization U).conjStarAlgEquiv (tensorCreation H h + tensorAnnihilation H h) =
      tensorCreation H (U h) + tensorAnnihilation H (U h) := by
  rw [map_add, secondQuantization_conj_creation, secondQuantization_conj_annihilation]

/-- Original-H full-Fock creation covariance as an actual operator conjugation. -/
@[simp] theorem fullSecondQuantization_conj_creation (U : H ≃ₗᵢ[ℂ] H) (h : H) :
    (fullSecondQuantization U).conjStarAlgEquiv (fullCreation H h) = fullCreation H (U h) := by
  apply ContinuousLinearMap.ext
  intro f
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, fullSecondQuantization_creation,
    LinearIsometryEquiv.apply_symm_apply]

/-- The original-H Hilbert adjoint is conjugated by the same full-Fock unitary. -/
@[simp] theorem fullSecondQuantization_conj_annihilation (U : H ≃ₗᵢ[ℂ] H) (h : H) :
    (fullSecondQuantization U).conjStarAlgEquiv (fullAnnihilation H h) =
      fullAnnihilation H (U h) := by
  change (fullSecondQuantization U).conjStarAlgEquiv (star (fullCreation H h)) =
    star (fullCreation H (U h))
  rw [map_star, fullSecondQuantization_conj_creation]

theorem fullSecondQuantization_conj_field (U : H ≃ₗᵢ[ℂ] H) (h : H) :
    (fullSecondQuantization U).conjStarAlgEquiv (fullCreation H h + fullAnnihilation H h) =
      fullCreation H (U h) + fullAnnihilation H (U h) := by
  rw [map_add, fullSecondQuantization_conj_creation, fullSecondQuantization_conj_annihilation]

/-- Vacuum-state invariance in the complete word realization of the original Hilbert space. -/
theorem fullSecondQuantization_vacuum_expectation (U : H ≃ₗᵢ[ℂ] H)
    (T : FullFock H →L[ℂ] FullFock H) :
    inner ℂ (fullVacuum H) ((fullSecondQuantization U).conjStarAlgEquiv T (fullVacuum H)) =
      inner ℂ (fullVacuum H) (T (fullVacuum H)) := by
  have hs : (fullSecondQuantization U).symm (fullVacuum H) = fullVacuum H := by
    apply (fullSecondQuantization U).injective
    simp
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, hs]
  calc
    inner ℂ (fullVacuum H) (fullSecondQuantization U (T (fullVacuum H))) =
      inner ℂ (fullSecondQuantization U (fullVacuum H))
        (fullSecondQuantization U (T (fullVacuum H))) := by rw [fullSecondQuantization_vacuum]
    _ = _ := (fullSecondQuantization U).inner_map_map _ _

end FreeProbability.Fock

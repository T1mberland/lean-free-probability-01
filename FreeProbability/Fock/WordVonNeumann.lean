import FreeProbability.Fock.GeneratedState
import Mathlib.Analysis.VonNeumannAlgebra.Basic

/-! # The literal generated word von Neumann algebra and its separating vacuum -/
noncomputable section
namespace FreeProbability.Fock

/-- The actual algebraic double commutant as a star subalgebra. -/
def wordSemicircularDoubleAlgebra (I : Type*) : StarSubalgebra ℂ (WordSpace I →L[ℂ] WordSpace I) :=
  StarSubalgebra.centralizer ℂ
    (StarSubalgebra.centralizer ℂ (semicircularAlgebra I : Set (WordSpace I →L[ℂ] WordSpace I)) : Set (WordSpace I →L[ℂ] WordSpace I))

theorem wordSemicircularDoubleAlgebra_coe (I : Type*) :
    (wordSemicircularDoubleAlgebra I : Set (WordSpace I →L[ℂ] WordSpace I)) =
      Set.centralizer (Set.centralizer (semicircularAlgebra I : Set (WordSpace I →L[ℂ] WordSpace I))) := by
  let C := StarSubalgebra.centralizer ℂ (semicircularAlgebra I : Set (WordSpace I →L[ℂ] WordSpace I))
  have hc : (C : Set (WordSpace I →L[ℂ] WordSpace I)) = Set.centralizer (semicircularAlgebra I : Set (WordSpace I →L[ℂ] WordSpace I)) := by
    rw [StarSubalgebra.coe_centralizer, StarMemClass.star_coe_eq, Set.union_self]
  have hd : (StarSubalgebra.centralizer ℂ (C : Set (WordSpace I →L[ℂ] WordSpace I)) : Set (WordSpace I →L[ℂ] WordSpace I)) = Set.centralizer (C : Set (WordSpace I →L[ℂ] WordSpace I)) := by
    rw [StarSubalgebra.coe_centralizer, StarMemClass.star_coe_eq, Set.union_self]
  change (StarSubalgebra.centralizer ℂ (C : Set (WordSpace I →L[ℂ] WordSpace I)) : Set (WordSpace I →L[ℂ] WordSpace I)) = _
  rw [hd, hc]

/-- The literal generated von Neumann algebra, without a WOT-closure identification premise. -/
def wordSemicircularVonNeumannAlgebra (I : Type*) : VonNeumannAlgebra (WordSpace I) where
  toStarSubalgebra := wordSemicircularDoubleAlgebra I
  centralizer_centralizer' := by
    change (wordSemicircularDoubleAlgebra I : Set (WordSpace I →L[ℂ] WordSpace I)).centralizer.centralizer =
      (wordSemicircularDoubleAlgebra I : Set (WordSpace I →L[ℂ] WordSpace I))
    rw [wordSemicircularDoubleAlgebra_coe, Set.centralizer_centralizer_centralizer]

theorem wordSemicircularVonNeumannAlgebra_mem_iff {I : Type*}
    {T : WordSpace I →L[ℂ] WordSpace I} :
    T ∈ wordSemicircularVonNeumannAlgebra I ↔
      T ∈ Set.centralizer (Set.centralizer (semicircularAlgebra I : Set (WordSpace I →L[ℂ] WordSpace I))) := by
  change T ∈ (wordSemicircularDoubleAlgebra I : Set (WordSpace I →L[ℂ] WordSpace I)) ↔ _
  rw [wordSemicircularDoubleAlgebra_coe]

/-- Full right-field cyclicity separates the vacuum on the literal double commutant. -/
theorem wordSemicircularVonNeumannAlgebra_commute_right {I : Type*}
    {T : WordSpace I →L[ℂ] WordSpace I} (hT : T ∈ wordSemicircularVonNeumannAlgebra I)
    (i : I) : Commute T (rightSemicircular i) := by
  rw [wordSemicircularVonNeumannAlgebra_mem_iff] at hT
  have hr : rightSemicircular i ∈ Set.centralizer (semicircularAlgebra I : Set (WordSpace I →L[ℂ] WordSpace I)) := by
    intro U hU
    exact (commute_right_of_mem_semicircularAlgebra hU i).eq
  exact (hT _ hr).symm

theorem wordSemicircularVonNeumannAlgebra_vacuum_faithful {I : Type*}
    {T : WordSpace I →L[ℂ] WordSpace I} (hT : T ∈ wordSemicircularVonNeumannAlgebra I)
    (hzero : vacuumExpectation (star T * T) = 0) : T = 0 := by
  apply eq_zero_of_commute_right_of_vacuum_eq_zero T
    (wordSemicircularVonNeumannAlgebra_commute_right hT)
  rw [vacuumExpectation_star_mul_self, sq_eq_zero_iff, Complex.ofReal_eq_zero,
    norm_eq_zero] at hzero
  exact hzero

end FreeProbability.Fock

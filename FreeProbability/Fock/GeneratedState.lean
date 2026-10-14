import FreeProbability.Fock.RightOperators

/-!
# Faithfulness on the generated semicircular polynomial algebra

The positive vacuum state is restricted to the actual generated star algebra.
Faithfulness is obtained from commuting right operators and cyclic Wick vectors;
it is not imposed as an assumption. Traciality is also proved on this polynomial algebra.
-/

noncomputable section
open scoped Classical InnerProductSpace ComplexOrder

namespace FreeProbability.Fock

variable {I : Type*}

/-- Every element of the generated left algebra commutes with every right generator. -/
theorem commute_right_of_mem_semicircularAlgebra
    {T : WordSpace I →L[ℂ] WordSpace I} (hT : T ∈ semicircularAlgebra I) (i : I) :
    Commute T (rightSemicircular i) := by
  have hle : semicircularAlgebra I ≤
      StarSubalgebra.centralizer ℂ (Set.range rightSemicircular) := by
    apply StarAlgebra.adjoin_le
    rintro _ ⟨j, rfl⟩
    change semicircular j ∈ StarSubalgebra.centralizer ℂ (Set.range rightSemicircular)
    rw [StarSubalgebra.mem_centralizer_iff]
    rintro _ ⟨k, rfl⟩
    constructor
    · exact (commute_semicircular_rightSemicircular j k).eq.symm
    · simpa [ContinuousLinearMap.star_eq_adjoint] using
        (commute_semicircular_rightSemicircular j k).eq.symm
  exact (((StarSubalgebra.mem_centralizer_iff ℂ).mp (hle hT)) _ ⟨i, rfl⟩).1.symm

/-- Right cyclicity makes the vacuum separating for the left generated algebra. -/
theorem eq_zero_of_commute_right_of_vacuum_eq_zero
    (T : WordSpace I →L[ℂ] WordSpace I)
    (hcomm : ∀ i, Commute T (rightSemicircular i))
    (hΩ : T (vacuum : WordSpace I) = 0) : T = 0 := by
  have hzero : reversal * T * reversal = 0 := by
    apply eq_zero_of_commute_semicircular_of_vacuum_eq_zero
    · intro i
      apply ContinuousLinearMap.ext
      intro f
      have h := congrArg (fun U : WordSpace I →L[ℂ] WordSpace I => reversal (U (reversal f)))
        (hcomm i).eq
      simpa [rightSemicircular, mul_apply_eq_comp] using h
    · simp [mul_apply_eq_comp, hΩ]
  apply ContinuousLinearMap.ext
  intro f
  have h := congrArg (fun U : WordSpace I →L[ℂ] WordSpace I => reversal (U (reversal f))) hzero
  simpa [mul_apply_eq_comp] using h

/-- Faithfulness of vacuum evaluation on the generated polynomial star algebra. -/
theorem vacuumExpectation_faithful_on_semicircularAlgebra
    {T : WordSpace I →L[ℂ] WordSpace I} (hT : T ∈ semicircularAlgebra I)
    (hzero : vacuumExpectation (star T * T) = 0) : T = 0 := by
  apply eq_zero_of_commute_right_of_vacuum_eq_zero T
    (commute_right_of_mem_semicircularAlgebra hT)
  rw [vacuumExpectation_star_mul_self, sq_eq_zero_iff, Complex.ofReal_eq_zero,
    norm_eq_zero] at hzero
  exact hzero

/-- The actual restricted positive vacuum probability space. -/
def generatedVacuumState (I : Type*) : StarProbabilitySpace (semicircularAlgebra I) where
  expectation := vacuumLinear.comp (semicircularAlgebra I).val.toLinearMap
  map_one := vacuumExpectation_one
  map_star T := vacuumExpectation_star (T : WordSpace I →L[ℂ] WordSpace I)
  positive T := (vacuumState I).positive (T : WordSpace I →L[ℂ] WordSpace I)

/-- The generated state is faithful, rather than merely positive. -/
theorem generatedVacuumState_isFaithful (I : Type*) :
    IsFaithful (generatedVacuumState I).toProbabilitySpace := by
  intro T hT
  apply Subtype.ext
  exact vacuumExpectation_faithful_on_semicircularAlgebra T.property hT

/-- A generator can be rotated past any element of the generated algebra. -/
theorem vacuumExpectation_semicircular_mul_comm (i : I)
    {T : WordSpace I →L[ℂ] WordSpace I} (hT : T ∈ semicircularAlgebra I) :
    vacuumExpectation (semicircular i * T) = vacuumExpectation (T * semicircular i) := by
  change inner ℂ vacuum (semicircular i (T vacuum)) =
    inner ℂ vacuum (T (semicircular i vacuum))
  calc
    inner ℂ vacuum (semicircular i (T vacuum)) = inner ℂ (semicircular i vacuum) (T vacuum) := by
      rw [← ContinuousLinearMap.adjoint_inner_right, adjoint_semicircular]
    _ = inner ℂ (rightSemicircular i vacuum) (T vacuum) := by
      rw [semicircular_vacuum, rightSemicircular_vacuum]
    _ = inner ℂ vacuum (rightSemicircular i (T vacuum)) := by
      rw [← ContinuousLinearMap.adjoint_inner_right, adjoint_rightSemicircular]
    _ = inner ℂ vacuum (T (rightSemicircular i vacuum)) := by
      have h := congrArg (fun U : WordSpace I →L[ℂ] WordSpace I => U vacuum)
        (commute_right_of_mem_semicircularAlgebra hT i).eq
      rw [show rightSemicircular i (T vacuum) = T (rightSemicircular i vacuum) from h.symm]
    _ = inner ℂ vacuum (T (semicircular i vacuum)) := by
      rw [semicircular_vacuum, rightSemicircular_vacuum]

/-- The vacuum is tracial on the generated polynomial star algebra. -/
theorem vacuumExpectation_mul_comm_on_semicircularAlgebra
    {T U : WordSpace I →L[ℂ] WordSpace I}
    (hT : T ∈ semicircularAlgebra I) (hU : U ∈ semicircularAlgebra I) :
    vacuumExpectation (T * U) = vacuumExpectation (U * T) := by
  induction hT using StarAlgebra.adjoin_induction generalizing U with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact vacuumExpectation_semicircular_mul_comm i hU
  | algebraMap c => simp [Algebra.algebraMap_eq_smul_one, vacuumExpectation, inner_smul_right]
  | add x y hx hy ihx ihy =>
    simp only [add_mul, mul_add, ← vacuumState_expectation, map_add]
    exact congrArg₂ (· + ·) (ihx hU) (ihy hU)
  | mul x y hx hy ihx ihy =>
    calc
      vacuumExpectation (x * y * U) = vacuumExpectation (y * U * x) := by
        rw [mul_assoc]; exact ihx ((semicircularAlgebra I).mul_mem hy hU)
      _ = vacuumExpectation (U * x * y) := by
        rw [mul_assoc]; exact ihy ((semicircularAlgebra I).mul_mem hU hx)
      _ = vacuumExpectation (U * (x * y)) := by rw [mul_assoc]
  | star x hx ih =>
    apply star_injective
    have h := ih (star_mem hU)
    simpa only [← vacuumExpectation_star, star_mul, star_star] using h.symm

end FreeProbability.Fock


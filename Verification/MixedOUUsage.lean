import FreeProbability.Fock.WickMixedSuffixGramFinsupp

noncomputable section
open scoped Classical
namespace FreeProbability.Examples
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

-- Degree zero, one and two coexist with arbitrary noncommuting 3-by-3 coefficients.
example (e : Fin 2 → H) (he : Orthonormal ℂ e) (t : ℝ) (ht : 0 ≤ t)
    (C : List (Fin 2) → Matrix (Fin 3) (Fin 3) ℂ) :
    0 ≤ Fock.actualFamilyWordOUMatrix e he t ht
      (Fock.matrixClosedWickAmplitude {[], [0], [0, 1]} C *
        star (Fock.matrixClosedWickAmplitude {[], [0], [0, 1]} C)) :=
  Fock.actualFamilyWordOUMatrix_mixed_amplitude_nonneg e he t ht {[], [0], [0, 1]} C

end FreeProbability.Examples

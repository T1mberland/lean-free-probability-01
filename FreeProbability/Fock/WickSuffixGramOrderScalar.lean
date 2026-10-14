import FreeProbability.Fock.WickSuffixGramOrderCardinality

/-! # Genuine positive scalar monotonicity and linear scalar-matrix embedding -/
noncomputable section
open scoped Classical ComplexOrder
namespace FreeProbability.Fock
variable {E ν : Type*} [Fintype ν] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Scalar monotonicity in the full canonical matrix cone, via the actual block space. -/
theorem matrixOperator_smul_scalar_mono (a b : ℝ) (hab : a ≤ b)
    (T : CStarMatrix ν ν (E →L[ℂ] E)) (hT : 0 ≤ T) : (a : ℂ) • T ≤ (b : ℂ) • T := by
  let Φ := hilbertMatrixStarAlgEquiv (N := ν) (E := E)
  apply (NonUnitalStarAlgHom.map_le_map_iff Φ Φ.injective).mp
  simp only [map_smul]
  apply smul_le_smul_of_nonneg_right
  · exact (RCLike.ofReal_le_ofReal (K := ℂ)).mpr hab
  · exact map_nonneg Φ hT

/-- Positive scalar multiplication preserves the entire canonical matrix order. -/
theorem matrixOperator_smul_mono (a : ℝ) (ha : 0 ≤ a)
    {T U : CStarMatrix ν ν (E →L[ℂ] E)} (hTU : T ≤ U) : (a : ℂ) • T ≤ (a : ℂ) • U := by
  let Φ := hilbertMatrixStarAlgEquiv (N := ν) (E := E)
  apply (NonUnitalStarAlgHom.map_le_map_iff Φ Φ.injective).mp
  simp only [map_smul]
  apply smul_le_smul_of_nonneg_left
  · exact (NonUnitalStarAlgHom.map_le_map_iff Φ Φ.injective).mpr hTU
  · exact (RCLike.ofReal_nonneg (K := ℂ)).mpr ha

variable {I : Type*}
/-- Actual linear scalar-matrix embedding, retaining sums of possibly singular marginals. -/
def matrixScalarEmbedLinear : Matrix ν ν ℂ →ₗ[ℂ] CStarMatrix ν ν (WordSpace I →L[ℂ] WordSpace I) :=
  (CStarMatrix.ofMatrixₗ (R := ℂ)).toLinearMap.comp
    (StarAlgHom.ofId ℂ (WordSpace I →L[ℂ] WordSpace I)).toLinearMap.mapMatrix

omit [Fintype ν] in
@[simp] theorem matrixScalarEmbedLinear_apply (C : Matrix ν ν ℂ) :
    matrixScalarEmbedLinear (I := I) C = matrixScalarEmbed C := by
  apply CStarMatrix.ext
  intro i j
  change algebraMap ℂ (WordSpace I →L[ℂ] WordSpace I) (C i j) = C i j • wick []
  rw [Algebra.algebraMap_eq_smul_one]
  rfl

end FreeProbability.Fock

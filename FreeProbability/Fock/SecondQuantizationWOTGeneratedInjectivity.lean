import FreeProbability.Fock.SecondQuantizationWOTGeneratedFaithfulness

/-! # Genuine injectivity of restricted WOT compression

This uses separating-vacuum faithfulness, not a norm-isometry inference about
WOT. Surjectivity and inverse bounded-WOT continuity remain separate obligations.
-/
noncomputable section
open scoped Classical
namespace FreeProbability.Fock
variable {I H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Compression cannot kill a nonzero included WOT operator for an orthonormal family. -/
theorem includedFamilyWOTCompression_eq_zero (V : H →ₗᵢ[ℂ] K) (e : I → H)
    (he : Orthonormal ℂ e) (T : tensorFamilyWOTAlgebra (fun i => V (e i)))
    (hzero : includedFamilyWOTCompression V e T = 0) : T = 0 := by
  apply Subtype.ext
  apply tensorFamilyWOTAlgebra_vacuum_separating (fun i => V (e i))
    (he.comp_linearIsometry V) T.property
  have hz : secondQuantizationCompression V T.val.toCLM = 0 :=
    congrArg (fun S : tensorFamilyWOTAlgebra e => S.val.toCLM) hzero
  have hi := DFunLike.congr_fun (tensorFamilyWOTAlgebra_inclusion_comp V e T.property)
    (tensorVacuum H)
  change T.val.toCLM (secondQuantizationIsometry V (tensorVacuum H)) =
    secondQuantizationIsometry V (secondQuantizationCompression V T.val.toCLM (tensorVacuum H)) at hi
  rw [secondQuantizationIsometry_vacuum, hz, zero_apply, map_zero] at hi
  exact hi

/-- The actual continuous restricted star homomorphism is injective on the entire WOT closure. -/
theorem includedFamilyWOTCompression_injective (V : H →ₗᵢ[ℂ] K) (e : I → H)
    (he : Orthonormal ℂ e) : Function.Injective (includedFamilyWOTCompression V e) := by
  intro T S hTS
  have hh : includedFamilyWOTCompression V e (T - S) = 0 :=
    (map_sub (includedFamilyWOTCompression V e).toAlgHom T S).trans
      ((congrArg (fun z : tensorFamilyWOTAlgebra e => z - includedFamilyWOTCompression V e S)
        hTS).trans (sub_self _))
  exact sub_eq_zero.mp (includedFamilyWOTCompression_eq_zero V e he (T - S) hh)

end FreeProbability.Fock

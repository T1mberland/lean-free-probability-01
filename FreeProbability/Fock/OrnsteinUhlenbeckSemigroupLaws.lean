import FreeProbability.Fock.OrnsteinUhlenbeckSemigroupDensity

/-! # Genuine zero-time and time-addition laws on the entire native C-star closure -/
noncomputable section
open scoped Classical
namespace FreeProbability.Fock
variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Genuine zero-time identity, on all operators in the literal generated closure. -/
theorem familyOUTimeContinuous_zero (e : I → H) (he : Orthonormal ℂ e) :
    familyOUTimeContinuous e he 0 (le_refl 0) = ContinuousLinearMap.id ℂ (tensorFamilyAlgebra e) := by
  apply familyContinuousLinearMap_ext_Wick e
  intro w
  change familyOUTime e he 0 (le_refl 0) (familyClosedWick e w) = familyClosedWick e w
  rw [familyOUTime_Wick]
  simp

/-- Actual additive-time semigroup law, established on Wick words and extended by genuine norm density. -/
theorem familyOUTimeContinuous_add (e : I → H) (he : Orthonormal ℂ e)
    (t u : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    (familyOUTimeContinuous e he t ht).comp (familyOUTimeContinuous e he u hu) =
      familyOUTimeContinuous e he (t + u) (add_nonneg ht hu) := by
  apply familyContinuousLinearMap_ext_Wick e
  intro w
  change familyOUTime e he t ht (familyOUTime e he u hu (familyClosedWick e w)) =
    familyOUTime e he (t + u) (add_nonneg ht hu) (familyClosedWick e w)
  have hs : familyOUTime e he t ht ((Real.exp (-u) : ℂ) ^ w.length • familyClosedWick e w) =
      (Real.exp (-u) : ℂ) ^ w.length • familyOUTime e he t ht (familyClosedWick e w) :=
    map_smul (familyOUTime e he t ht).toLinearMap _ _
  have hc : (Real.exp (-(t + u)) : ℂ) ^ w.length =
      (Real.exp (-u) : ℂ) ^ w.length * (Real.exp (-t) : ℂ) ^ w.length := by
    rw [neg_add, Real.exp_add, Complex.ofReal_mul, mul_pow, mul_comm]
  calc
    _ = familyOUTime e he t ht ((Real.exp (-u) : ℂ) ^ w.length • familyClosedWick e w) :=
      congrArg (familyOUTime e he t ht) (familyOUTime_Wick e he u hu w)
    _ = (Real.exp (-u) : ℂ) ^ w.length • familyOUTime e he t ht (familyClosedWick e w) := hs
    _ = (Real.exp (-u) : ℂ) ^ w.length • ((Real.exp (-t) : ℂ) ^ w.length • familyClosedWick e w) :=
      congrArg ((Real.exp (-u) : ℂ) ^ w.length • ·) (familyOUTime_Wick e he t ht w)
    _ = ((Real.exp (-u) : ℂ) ^ w.length * (Real.exp (-t) : ℂ) ^ w.length) • familyClosedWick e w :=
      smul_smul _ _ _
    _ = (Real.exp (-(t + u)) : ℂ) ^ w.length • familyClosedWick e w :=
      congrArg (· • familyClosedWick e w) hc.symm
    _ = _ := (familyOUTime_Wick e he (t + u) (add_nonneg ht hu) w).symm

/-- Pointwise zero-time identity of the genuine completely positive native OU map. -/
@[simp] theorem familyOUTime_zero (e : I → H) (he : Orthonormal ℂ e) (T : tensorFamilyAlgebra e) :
    familyOUTime e he 0 (le_refl 0) T = T :=
  DFunLike.congr_fun (familyOUTimeContinuous_zero e he) T

/-- Pointwise time-addition identity of the genuine completely positive self-maps. -/
theorem familyOUTime_add (e : I → H) (he : Orthonormal ℂ e)
    (t u : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) (T : tensorFamilyAlgebra e) :
    familyOUTime e he t ht (familyOUTime e he u hu T) =
      familyOUTime e he (t + u) (add_nonneg ht hu) T :=
  DFunLike.congr_fun (familyOUTimeContinuous_add e he t u ht hu) T

/-- Every native OU self-map remains unital at its actual nonnegative time. -/
@[simp] theorem familyOUTime_one (e : I → H) (he : Orthonormal ℂ e) (t : ℝ) (ht : 0 ≤ t) :
    familyOUTime e he t ht 1 = 1 := familyOU_one e he _ _ _

theorem norm_familyOUTime_le (e : I → H) (he : Orthonormal ℂ e) (t : ℝ) (ht : 0 ≤ t)
    (T : tensorFamilyAlgebra e) : ‖familyOUTime e he t ht T‖ ≤ ‖T‖ := norm_familyOU_le e he _ _ _ T

theorem familyOUTime_expectation (e : I → H) (he : Orthonormal ℂ e) (t : ℝ) (ht : 0 ≤ t)
    (T : tensorFamilyAlgebra e) :
    (tensorFamilyVacuumState e).expectation (familyOUTime e he t ht T) =
      (tensorFamilyVacuumState e).expectation T := familyOU_expectation e he _ _ _ T

end FreeProbability.Fock

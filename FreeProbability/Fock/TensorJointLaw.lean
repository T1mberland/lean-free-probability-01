import FreeProbability.Fock.TensorCStarModel

/-! # Literal joint Wick and Catalan laws on the completed-tensor Fock realization -/

noncomputable section
open scoped Classical
open FreeProbability.NoncrossingPairing

namespace FreeProbability.Fock

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem tensorVacuumState_operatorWord (w : List (fullFockBasisSet H)) :
    (tensorVacuumState H).expectation (w.map (tensorSemicircular H)).prod =
      vacuumExpectation (operatorWord w) := by
  change vacuumExpectation ((tensorOperatorEquiv H).symm (w.map (tensorSemicircular H)).prod) = _
  rw [map_list_prod, List.map_map]
  have he : (tensorOperatorEquiv H).symm ∘ tensorSemicircular H = semicircular := by
    funext i
    rw [Function.comp_apply, tensorSemicircular_eq_transport, StarAlgEquiv.symm_apply_apply]
  rw [he]
  rfl

/-- Exact all-order joint law with one actual covariance factor for each two-point block. -/
theorem tensorVacuumState_joint_free_wick (n : ℕ) (a : Fin n → fullFockBasisSet H) :
    (tensorVacuumState H).expectation (List.ofFn (fun k => tensorSemicircular H (a k))).prod =
      ∑ p : NoncrossingPairing n, ∏ e ∈ pairingPairs p,
        if a e.1 = a e.2 then (1 : ℂ) else 0 := by
  calc
    _ = vacuumExpectation (operatorWord (List.ofFn a)) := by
      simpa only [List.map_ofFn, Function.comp_def] using tensorVacuumState_operatorWord H (List.ofFn a)
    _ = _ := by
      convert joint_free_wick n a using 1
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.prod_congr rfl
      intro e he
      by_cases h : a e.1 = a e.2 <;> simp [h]

/-- Literal joint law inside the concrete faithful tracial tensor C-star probability space. -/
theorem tensorClosedVacuumState_joint_free_wick (n : ℕ) (a : Fin n → fullFockBasisSet H) :
    (tensorClosedVacuumState H).expectation
      (List.ofFn (fun k => tensorClosedSemicircular H (a k))).prod =
      ∑ p : NoncrossingPairing n, ∏ e ∈ pairingPairs p,
        if a e.1 = a e.2 then (1 : ℂ) else 0 := by
  change (tensorVacuumState H).expectation ((tensorClosedSemicircularAlgebra H).val
    (List.ofFn (fun k => tensorClosedSemicircular H (a k))).prod) = _
  rw [map_list_prod, List.map_ofFn]
  exact tensorVacuumState_joint_free_wick H n a

/-- Actual marginal moments in the full tensor-domain realization. -/
theorem tensorVacuumState_semicircular_pow (i : fullFockBasisSet H) (n : ℕ) :
    (tensorVacuumState H).expectation (tensorSemicircular H i ^ n) =
      if Even n then (catalan (n / 2) : ℂ) else 0 := by
  change vacuumExpectation ((tensorOperatorEquiv H).symm (tensorSemicircular H i ^ n)) = _
  rw [map_pow, tensorSemicircular_eq_transport, StarAlgEquiv.symm_apply_apply]
  exact vacuumExpectation_semicircular_pow i n

/-- Actual even Catalan moments in the faithful tracial C-star tensor realization. -/
theorem tensorClosedVacuumState_even_pow (i : fullFockBasisSet H) (n : ℕ) :
    (tensorClosedVacuumState H).expectation (tensorClosedSemicircular H i ^ (2 * n)) =
      (catalan n : ℂ) := by
  change (tensorVacuumState H).expectation (tensorSemicircular H i ^ (2 * n)) = _
  rw [tensorVacuumState_semicircular_pow]
  simp

end FreeProbability.Fock

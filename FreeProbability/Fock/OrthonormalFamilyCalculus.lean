import FreeProbability.Fock.OrthonormalFamilyState
import FreeProbability.Fock.PolynomialIntegrationByParts

/-! # Vacuum grading and polynomial integration by parts in adapted full Fock models -/

noncomputable section
open scoped Classical InnerProductSpace TensorProduct

namespace FreeProbability.Fock.OrthonormalFamilyExtension

variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {e : I → H} (d : OrthonormalFamilyExtension e)

/-- The actual unit vacuum vector in the adapted complete Fock model. -/
def vacuum : d.Space := Fock.vacuum

@[simp] theorem norm_vacuum : ‖d.vacuum‖ = 1 := Fock.norm_vacuum

/-- The degree-zero sector is isometrically the scalar Hilbert space. -/
def scalarLevel : ℂ ≃ₗᵢ[ℂ] WordLevel d.indices 0 := scalarLevelEquiv

/-- Degree-zero scalar tensors are exactly scalar multiples of the actual vacuum. -/
@[simp] theorem scalar_level_embedding (c : ℂ) :
    levelEmbedding 0 (d.scalarLevel c) = c • d.vacuum := by
  change levelEmbedding 0 (scalarLevelIsometry c) = _
  simp [scalarLevelIsometry, LinearIsometry.toSpanSingleton_apply, levelEmbedding_single,
    emptyTuple, vacuum, Fock.vacuum]

/-- The direct-sum vacuum lies exactly in degree zero with scalar coordinate one. -/
@[simp] theorem grading_vacuum :
    d.grading d.vacuum = lp.single 2 0 (d.scalarLevel 1) := by
  apply d.grading.symm.injective
  rw [LinearIsometryEquiv.symm_apply_apply]
  change d.vacuum = lengthDecomposition.symm (lp.single 2 0 (d.scalarLevel 1))
  rw [lengthDecomposition_symm_single, d.scalar_level_embedding, one_smul]

/-- Creation by every original vector has its actual Hilbert adjoint annihilating the vacuum. -/
@[simp] theorem annihilation_vacuum (h : H) : d.annihilation h d.vacuum = 0 :=
  basisAnnihilation_vacuum d.basis h

@[simp] theorem centered (i : I) : d.state.expectation (d.generator i) = 0 := by
  simpa using d.odd_moment i 0

@[simp] theorem variance_one (i : I) : d.state.expectation (d.generator i ^ 2) = 1 := by
  simpa using d.even_moment i 1

/-- A finite ordered product of the prescribed fields. -/
def operatorWord (w : List I) : d.Space →L[ℂ] d.Space := (w.map d.field).prod

/-- Original-family words act as the corresponding canonical words in the extended basis. -/
theorem operatorWord_eq (w : List I) : d.operatorWord w = Fock.operatorWord (w.map d.index) := by
  simp only [operatorWord, Fock.operatorWord, List.map_map, Function.comp_def]
  congr 2
  funext i
  exact d.field_eq_semicircular i

/-- Exact word integration by parts, retaining the original family's indices. -/
theorem word_integrationByParts (i : I) (w : List I) :
    vacuumExpectation (d.operatorWord (i :: w)) =
      ∑ k : Fin w.length, if i = w.get k then
        vacuumExpectation (d.operatorWord (w.take k.val)) *
          vacuumExpectation (d.operatorWord (w.drop (k.val + 1))) else 0 := by
  simp only [d.operatorWord_eq, List.map_cons]
  rw [vacuumExpectation_operatorWord_cons]
  apply Fintype.sum_equiv (finCongr (List.length_map (as := w) d.index))
  intro k
  have hk : (finCongr (List.length_map (as := w) d.index) k).val = k.val := rfl
  simp only [hk, List.get_eq_getElem, List.getElem_map,
    ← List.map_take, ← List.map_drop, d.index_injective.eq_iff]

/-- Free integration by parts for every polynomial in the original orthonormal family. -/
theorem polynomial_integrationByParts (i : I) (p : WordPolynomial ℂ I) :
    (vacuumState d.indices).expectation (d.field i * evaluate d.field p) =
      tensorPolynomialExpectation (vacuumState d.indices).toProbabilitySpace d.field
        (freeDifferenceQuotient i p) := by
  induction p using MonoidAlgebra.induction_linear with
  | zero => simp [vacuumExpectation]
  | add p q hp hq =>
    simp only [map_add, mul_add]
    exact congrArg₂ (· + ·) hp hq
  | single w c =>
    obtain ⟨w, rfl⟩ := FreeMonoid.ofList.surjective w
    rw [evaluate_single, freeDifferenceQuotient_single]
    simp only [mul_smul_comm, map_smul]
    congr 1
    change vacuumExpectation (d.operatorWord (i :: w)) = _
    rw [d.word_integrationByParts, wordDifferenceQuotient_eq_sum, map_sum]
    apply Finset.sum_congr rfl
    intro k _
    by_cases h : i = w.get k
    · simp only [List.get_eq_getElem] at h
      simp [h, tensorPolynomialExpectation_tmul, wordMonomial, evaluate_single, operatorWord]
    · simp only [List.get_eq_getElem] at h
      simp [h]

/-- Polynomial evaluation in the actual family-generated algebra agrees with the field operators. -/
theorem coe_evaluate_generator (p : WordPolynomial ℂ I) :
    d.generatedAlgebra.val (evaluate d.generator p) = evaluate d.field p := by
  induction p using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq =>
    simp only [map_add]
    exact congrArg₂ (· + ·) hp hq
  | single w c =>
    obtain ⟨w, rfl⟩ := FreeMonoid.ofList.surjective w
    simp only [evaluate_single, map_smul, map_list_prod, List.map_map]
    rfl

/-- Tensor expectation is the actual product of the restricted vacuum expectations. -/
theorem tensor_expectation :
    tensorPolynomialExpectation d.state.toProbabilitySpace d.generator =
      tensorPolynomialExpectation (vacuumState d.indices).toProbabilitySpace d.field := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul p q =>
    simp only [tensorPolynomialExpectation_tmul]
    change vacuumExpectation (d.generatedAlgebra.val (evaluate d.generator p)) *
      vacuumExpectation (d.generatedAlgebra.val (evaluate d.generator q)) = _
    rw [d.coe_evaluate_generator, d.coe_evaluate_generator]
    rfl
  | add x y hx hy => simp [map_add, hx, hy]

/-- Polynomial IBP inside the literal faithful tracial family-generated C-star probability space. -/
theorem state_polynomial_integrationByParts (i : I) (p : WordPolynomial ℂ I) :
    d.state.expectation (d.generator i * evaluate d.generator p) =
      tensorPolynomialExpectation d.state.toProbabilitySpace d.generator
        (freeDifferenceQuotient i p) := by
  rw [d.tensor_expectation]
  change vacuumExpectation (d.generatedAlgebra.val (d.generator i * evaluate d.generator p)) = _
  rw [map_mul, d.coe_evaluate_generator]
  exact d.polynomial_integrationByParts i p

end FreeProbability.Fock.OrthonormalFamilyExtension

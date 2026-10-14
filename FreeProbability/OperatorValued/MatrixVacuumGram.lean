import FreeProbability.OperatorValued.MatrixCauchyImaginary

/-! # Strict vacuum Gram positivity for invertible bounded-operator matrices -/

noncomputable section
open scoped Classical ComplexOrder
open Matrix
namespace FreeProbability.Fock

variable {I n : Type*} [Fintype n] [DecidableEq n]

/-- The actual action of a matrix of bounded Fock operators on finite Fock vectors. -/
def matrixVacuumApply (T : Matrix n n (WordSpace I →L[ℂ] WordSpace I))
    (v : n → WordSpace I) : n → WordSpace I := fun r => ∑ c, T r c (v c)

omit [DecidableEq n] in
theorem matrixVacuumApply_mul (T S : Matrix n n (WordSpace I →L[ℂ] WordSpace I))
    (v : n → WordSpace I) :
    matrixVacuumApply (T * S) v = matrixVacuumApply T (matrixVacuumApply S v) := by
  funext r
  simp only [matrixVacuumApply, Matrix.mul_apply, _root_.sum_apply,
    mul_apply_eq_comp, map_sum]
  rw [Finset.sum_comm]

@[simp] theorem matrixVacuumApply_one (v : n → WordSpace I) : matrixVacuumApply 1 v = v := by
  funext r
  simp [matrixVacuumApply, Matrix.one_apply, apply_ite, ite_apply]

omit [DecidableEq n] in
@[simp] theorem matrixVacuumApply_zero (T : Matrix n n (WordSpace I →L[ℂ] WordSpace I)) :
    matrixVacuumApply T 0 = 0 := by
  funext r
  change (∑ c, T r c 0) = 0
  simp

/-- An invertible operator matrix acts injectively on finite vectors of Fock space. -/
theorem matrixVacuumApply_eq_zero_iff (T : Matrix n n (WordSpace I →L[ℂ] WordSpace I))
    (hT : IsUnit T) (v : n → WordSpace I) : matrixVacuumApply T v = 0 ↔ v = 0 := by
  constructor
  · intro hv
    obtain ⟨u, rfl⟩ := hT
    have h := congrArg (matrixVacuumApply (↑u⁻¹ : Matrix n n (WordSpace I →L[ℂ] WordSpace I))) hv
    simpa only [← matrixVacuumApply_mul, Units.inv_mul, matrixVacuumApply_one,
      matrixVacuumApply_zero] using h
  · intro hv
    rw [hv, matrixVacuumApply_zero]

omit [DecidableEq n] in
/-- The Gram quadratic form is exactly the sum of squared norms of the actual
matrix action on the scalar multiples of the vacuum. -/
theorem matrixVacuumGram_quadratic (T : Matrix n n (WordSpace I →L[ℂ] WordSpace I))
    (v : n → ℂ) :
    star v ⬝ᵥ (matrixExpectation (vacuumState I).toProbabilitySpace (Tᴴ * T) *ᵥ v) =
      ((∑ r, ‖matrixVacuumApply T (fun j => v j • vacuum) r‖ ^ 2 : ℝ) : ℂ) := by
  rw [matrixExpectation_quadratic, ← mulVec_mulVec, dotProduct_mulVec,
    vecMul_conjTranspose T (star (algebraMap ℂ (WordSpace I →L[ℂ] WordSpace I) ∘ v)),
    star_star, dotProduct, map_sum, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [Pi.star_apply]
  change vacuumExpectation (star _ * _) = _
  rw [vacuumExpectation_star_mul_self, ← Complex.ofReal_pow]
  congr 2
  simp [matrixVacuumApply, mulVec, dotProduct, Function.comp_apply,
    Algebra.algebraMap_eq_smul_one, _root_.sum_apply,
    ]

/-- Invertible matrices of genuine bounded Fock operators have strictly positive
vacuum Gram matrices, without faithfulness of the vacuum state on all operators. -/
theorem matrixVacuumGram_posDef (T : Matrix n n (WordSpace I →L[ℂ] WordSpace I)) (hT : IsUnit T) :
    (matrixExpectation (vacuumState I).toProbabilitySpace (Tᴴ * T)).PosDef := by
  apply PosDef.of_dotProduct_mulVec_pos (matrixExpectation_gram_posSemidef (vacuumState I) T).isHermitian
  intro v hv
  rw [matrixVacuumGram_quadratic, Complex.zero_lt_real]
  have hvec : (fun j => v j • (vacuum : WordSpace I)) ≠ 0 := by
    intro h
    apply hv
    funext j
    have hj := congrArg (fun f => ‖f j‖) h
    simpa [norm_smul, norm_vacuum] using hj
  have hnonzero : matrixVacuumApply T (fun j => v j • vacuum) ≠ 0 :=
    fun h => hvec ((matrixVacuumApply_eq_zero_iff T hT _).mp h)
  obtain ⟨r, hr⟩ : ∃ r, matrixVacuumApply T (fun j => v j • vacuum) r ≠ 0 := by
    by_contra h
    apply hnonzero
    funext r
    simpa using not_exists.mp h r
  exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨r, Finset.mem_univ r, sq_pos_of_pos (norm_pos_iff.mpr hr)⟩

end FreeProbability.Fock

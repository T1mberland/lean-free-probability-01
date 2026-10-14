import FreeProbability.Fock.FiniteDepthMatrixPropagation
import FreeProbability.OperatorValued.OperatorRetainedPowers

/-! # Actual retained powers of shifted matrix Fock pencils -/
noncomputable section
open scoped Classical
namespace FreeProbability.Fock
variable {I n : Type*} [Fintype I] [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
theorem matrixDepthSpace_mono {L M : ℕ} (h : L ≤ M) :
    matrixDepthSpace (n := n) (I := I) L ≤ matrixDepthSpace M := by
  intro f hf j
  exact depthSpace_mono h (hf j)

/-- Shifting by a scalar preserves the genuine one-level propagation property. -/
theorem shiftedPencil_mem_depth (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ)
    (c : ℂ) (L : ℕ) {f : HilbertMatrixSpace n (WordSpace I)}
    (hf : f ∈ matrixDepthSpace L) :
    (finiteDepthPencilOperator C₀ C + c • 1) f ∈ matrixDepthSpace (L + 1) := by
  rw [add_apply, smul_apply]
  apply Submodule.add_mem
  · exact finiteDepthPencilOperator_mem_depth C₀ C L hf
  · exact Submodule.smul_mem _ c (matrixDepthSpace_mono (Nat.le_succ L) hf)

/-- Powers of the actual shifted pencil propagate vacuum-level vectors by at most their degree. -/
theorem shiftedPencil_pow_mem_depth (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ)
    (c : ℂ) {x : HilbertMatrixSpace n (WordSpace I)} (hx : x ∈ matrixDepthSpace 0)
    (k : ℕ) : ( (finiteDepthPencilOperator C₀ C + c • 1) ^ k) x ∈ matrixDepthSpace k := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp]
    exact shiftedPencil_mem_depth C₀ C c k ih

/-- The literal finite-depth compression agrees on all powers through the retained depth. -/
theorem finiteDepth_shiftedPencil_retained_powers (C₀ : Matrix n n ℂ)
    (C : I → Matrix n n ℂ) (c : ℂ) (L : ℕ)
    {x : HilbertMatrixSpace n (WordSpace I)} (hx : x ∈ matrixDepthSpace 0) :
    ∀ k ≤ L,
      ((matrixDepthProjection (n := n) (I := I) L * (finiteDepthPencilOperator C₀ C + c • 1) *
          matrixDepthProjection (n := n) (I := I) L) ^ k) x =
        ((finiteDepthPencilOperator C₀ C + c • 1) ^ k) x := by
  apply operator_sandwich_pow_apply_eq
  intro k hk
  apply (matrixDepthProjection_eq_self_iff L _).mpr
  exact matrixDepthSpace_mono hk (shiftedPencil_pow_mem_depth C₀ C c hx k)

end FreeProbability.Fock
